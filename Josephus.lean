-- This module serves as the root of the `Josephus` library.
-- Import modules here that should be built as part of the library.
import Josephus.Basic
import Mathlib.Tactic

def isEven (n : ℕ) : Bool := Even n

-- ∀n ∈ ℕ, n > 0 → n < 2 * n.
lemma pos_mul2_gt
  (n : ℕ)
  (h : 0 < n)
  : n < 2 * n :=
by
  rw [Nat.mul_comm 2]
  rw [Nat.mul_succ n 1]
  simp
  exact h

-- ∀n ∈ ℕ, ¬n = 0 → n > 0
lemma nonzero_nat_pos (n : ℕ) (h : ¬n = 0) : n > 0 :=
  by cases n with
    | zero => contradiction
    | succ _ => exact Nat.zero_lt_succ _

-- The Josephus Problem's recurrence relation from *Concrete Mathematics*
-- by Graham, Knuth, & Patashnik, 2nd ed., pgs. 8-10.
-- Any number of the form (n + 1) * 2 is even, and (n + 1) * 2 + 1 is odd.
-- The n + 1 is necessary to set up induction, which is used in the lemma
-- nonzero_nat_pos.
def J (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 1 =>
    if isEven (n + 1) then
      2 * J ((n + 1) / 2) - 1
    else
      2 * J ((n + 1) / 2) + 1
decreasing_by
  all_goals
    simp_wf
    apply Nat.div_lt_of_lt_mul
    apply pos_mul2_gt
    · by_cases h : n = 0
      · rw [h]; norm_num
      · apply nonzero_nat_pos at h
        exact Nat.zero_lt_succ n
