import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Abel

/-! # Coefficient-controlled splitting of cyclic word differences -/

noncomputable section

namespace Langlands.CyclicWords

open FreeMonoid Relation

/-- A word in two letters. -/
abbrev Word := FreeMonoid Bool

/-- Noncommutative polynomials in two letters with coefficients in `F`. -/
abbrev WordPolynomial (F : Type*) [Semiring F] := MonoidAlgebra F Word

/-- An elementary cyclic rotation moves the first letter to the end. -/
inductive Rotate : Word → Word → Prop
  | step (b : Bool) (w : Word) : Rotate (of b * w) (w * of b)

/-- The equivalence class of a word under cyclic rotation. -/
def CyclicWord := Quotient (EqvGen.setoid Rotate)

/-- Regard a word as a cyclic word. -/
def cycle (w : Word) : CyclicWord := Quotient.mk _ w

private theorem cycle_step (b : Bool) (w : Word) : cycle (of b * w) = cycle (w * of b) :=
  Quotient.sound (.rel _ _ (.step b w))

theorem cycle_mul_comm (p q : Word) : cycle (p * q) = cycle (q * p) := by
  induction p using FreeMonoid.recOn generalizing q with
  | one => simp
  | of_mul b w ih =>
    calc
      cycle ((of b * w) * q) = cycle ((w * q) * of b) := by rw [mul_assoc, cycle_step]
      _ = cycle ((q * of b) * w) := by rw [mul_assoc w q, ih]
      _ = cycle (q * (of b * w)) := by rw [mul_assoc]

private theorem length_eq_of_eqvGen {p q : Word} (h : EqvGen Rotate p q) : p.length = q.length := by
  induction h with
  | rel _ _ h => cases h; simp [length_mul, Nat.add_comm]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Trace

variable (F : Type*) [CommSemiring F]

/-- The coefficient of a cyclic word is the sum of coefficients of its representatives. -/
def cyclicTrace : WordPolynomial F →ₗ[F] CyclicWord →₀ F :=
  (Finsupp.lmapDomain F F cycle).comp (MonoidAlgebra.coeffLinearEquiv F).toLinearMap

@[simp] theorem cyclicTrace_single (w : Word) (a : F) :
    cyclicTrace F (MonoidAlgebra.single w a) = Finsupp.single (cycle w) a := by
  change Finsupp.mapDomain cycle (Finsupp.single w a) = _
  exact Finsupp.mapDomain_single

/-- The cyclic trace identifies either order of a product. -/
theorem cyclicTrace_mul_comm (p q : WordPolynomial F) : cyclicTrace F (p * q) = cyclicTrace F (q * p) := by
  induction p using MonoidAlgebra.induction_on with
  | of p =>
    induction q using MonoidAlgebra.induction_on with
    | of q =>
      change cyclicTrace F (MonoidAlgebra.single p 1 * MonoidAlgebra.single q 1) =
        cyclicTrace F (MonoidAlgebra.single q 1 * MonoidAlgebra.single p 1)
      simp [cycle_mul_comm p q]
    | add x y hx hy => simp only [mul_add, add_mul, map_add, hx, hy]
    | smul a x hx => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hx]
  | add x y hx hy => simp only [mul_add, add_mul, map_add, hx, hy]
  | smul a x hx => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hx]

/-- A polynomial supported on words of one length. -/
def HasWordLength (p : WordPolynomial F) (n : ℕ) : Prop :=
  ∀ w : Word, w.length ≠ n → p.coeff w = 0

end Trace

section Splitting

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

private abbrev monomial (w : Word) : WordPolynomial F := MonoidAlgebra.single w 1

/-- The two generators of the word polynomial algebra. -/
def letter (b : Bool) : WordPolynomial F := monomial (of b)

private def commutator (a b : WordPolynomial F) : WordPolynomial F := a * b - b * a

private def Controlled (n : ℕ) (p : WordPolynomial F) : Prop :=
  HasWordLength F p n ∧ ∀ w : Word, ‖p.coeff w‖ ≤ 1

omit [IsUltrametricDist F] in
private theorem controlled_zero (n : ℕ) : Controlled (F := F) n 0 :=
  ⟨fun _ _ => rfl, fun _ => by simp⟩

omit [IsUltrametricDist F] in
private theorem controlled_monomial (w : Word) : Controlled w.length (monomial (F := F) w) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv
    change Finsupp.single w (1 : F) v = 0
    rw [Finsupp.single_apply, ite_eq_right (fun h => hv (congrArg FreeMonoid.length h.symm))]
  · intro v
    change ‖Finsupp.single w (1 : F) v‖ ≤ 1
    rw [Finsupp.single_apply]
    split <;> simp

omit [IsUltrametricDist F] in
private theorem Controlled.neg {n : ℕ} {p : WordPolynomial F} (hp : Controlled n p) : Controlled n (-p) :=
  ⟨fun w hw => by simp [hp.1 w hw], fun w => by simpa using hp.2 w⟩

private theorem Controlled.add {n : ℕ} {p q : WordPolynomial F} (hp : Controlled n p)
    (hq : Controlled n q) : Controlled n (p + q) :=
  ⟨fun w hw => by simp [hp.1 w hw, hq.1 w hw], fun w =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp.2 w) (hq.2 w))⟩

private theorem split_related {p q : Word} (h : EqvGen Rotate p q) :
    ∃ a b : WordPolynomial F, Controlled (p.length - 1) a ∧ Controlled (p.length - 1) b ∧
      monomial p - monomial q = commutator a (letter false) + commutator b (letter true) := by
  induction h with
  | rel p q h =>
    cases h with
    | step v w =>
      have hl : (of v * w).length - 1 = w.length := by simp [length_mul, Nat.add_comm]
      cases v
      · refine ⟨-monomial w, 0, hl ▸ ?_, controlled_zero _, ?_⟩
        · exact (controlled_monomial w).neg
        · simp [commutator, letter, neg_mul, mul_neg, sub_eq_add_neg, add_comm]
      · refine ⟨0, -monomial w, controlled_zero _, hl ▸ ?_, ?_⟩
        · exact (controlled_monomial w).neg
        · simp [commutator, letter, neg_mul, mul_neg, sub_eq_add_neg, add_comm]
  | refl p => exact ⟨0, 0, controlled_zero _, controlled_zero _, by simp [commutator]⟩
  | symm p q h ih =>
    obtain ⟨a, b, ha, hb, hab⟩ := ih
    have hlen := length_eq_of_eqvGen h
    refine ⟨-a, -b, by rw [← hlen]; exact ha.neg, by rw [← hlen]; exact hb.neg, ?_⟩
    simp only [commutator, neg_mul, mul_neg] at hab ⊢
    rw [← neg_sub (monomial (F := F) p) (monomial q), hab]
    abel
  | trans p q r hpq _ ih₁ ih₂ =>
    obtain ⟨a, b, ha, hb, hab⟩ := ih₁
    obtain ⟨c, d, hc, hd, hcd⟩ := ih₂
    rw [← length_eq_of_eqvGen hpq] at hc hd
    refine ⟨a + c, b + d, ha.add hc, hb.add hd, ?_⟩
    have h := congrArg₂ (· + ·) hab hcd
    dsimp only [commutator] at h ⊢
    rw [add_mul, add_mul, mul_add, mul_add]
    rw [show monomial (F := F) p - monomial r =
      (monomial p - monomial q) + (monomial q - monomial r) by abel, h]
    abel

private theorem existence_word_splitting (w : Word) :
    ∃ a b : WordPolynomial F, Controlled (w.length - 1) a ∧ Controlled (w.length - 1) b ∧
      monomial w - monomial (Quotient.out (cycle w)) =
        commutator a (letter false) + commutator b (letter true) := by
  apply split_related
  exact Quotient.exact (Quotient.out_eq (cycle w)).symm

/-- A homogeneous polynomial with zero cyclic trace splits as a sum of
commutators with the two letters, preserving the coefficient bound. -/
def CyclicWordSplittingStatement (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] : Prop :=
  ∀ (n : ℕ) (C : ℝ), 0 ≤ C → ∀ p : WordPolynomial F, HasWordLength F p (n + 1) →
    (∀ w, ‖p.coeff w‖ ≤ C) → cyclicTrace F p = 0 →
    ∃ a b : WordPolynomial F, HasWordLength F a n ∧ HasWordLength F b n ∧
      (∀ w, ‖a.coeff w‖ ≤ C ∧ ‖b.coeff w‖ ≤ C) ∧
      p = (a * letter false - letter false * a) + (b * letter true - letter true * b)

set_option maxHeartbeats 1200000 in
theorem cyclicWordSplitting (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] :
    CyclicWordSplittingStatement F := by
  classical
  intro n C hC p hp hBound hTrace
  choose a b ha hb hab using existence_word_splitting (F := F)
  let left := Finsupp.linearCombination F a
  let right := Finsupp.linearCombination F b
  let rep := Finsupp.linearCombination F (fun w : CyclicWord => monomial (F := F) (Quotient.out w))
  have hid (q : WordPolynomial F) : q - rep (cyclicTrace F q) =
      commutator (left q.coeff) (letter false) + commutator (right q.coeff) (letter true) := by
    induction q using MonoidAlgebra.induction_on with
    | of q =>
      change monomial q - rep (cyclicTrace F (monomial q)) =
        commutator (left (Finsupp.single q 1)) (letter false) + commutator (right (Finsupp.single q 1)) (letter true)
      simpa [left, right, rep, Finsupp.linearCombination_single] using hab q
    | add q q' hq hq' =>
      have h := congrArg₂ (· + ·) hq hq'
      simp only [map_add, MonoidAlgebra.coeff_add, commutator, add_mul, mul_add] at h ⊢
      rw [show q + q' - (rep (cyclicTrace F q) + rep (cyclicTrace F q')) =
        (q - rep (cyclicTrace F q)) + (q' - rep (cyclicTrace F q')) by abel, h]
      abel
    | smul z q hq =>
      have h := congrArg (fun u : WordPolynomial F => z • u) hq
      simpa only [map_smul, MonoidAlgebra.coeff_smul, commutator, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm]
        using h
  have hSupport (w : Word) (hw : w ∈ p.coeff.support) : w.length = n + 1 :=
    not_ne_iff.mp (fun hn => (Finsupp.mem_support_iff.mp hw) (hp w hn))
  have hSum (g : Word → WordPolynomial F) (hg : ∀ w, Controlled (w.length - 1) (g w)) :
      HasWordLength F (Finsupp.linearCombination F g p.coeff) n ∧
        ∀ w, ‖(Finsupp.linearCombination F g p.coeff).coeff w‖ ≤ C := by
    have hCoeff (w : Word) : (Finsupp.linearCombination F g p.coeff).coeff w =
        ∑ v ∈ p.coeff.support, p.coeff v * (g v).coeff w := by
      let coeffAt : WordPolynomial F →ₗ[F] F := (Finsupp.lapply w).comp (MonoidAlgebra.coeffLinearEquiv F).toLinearMap
      change coeffAt (Finsupp.linearCombination F g p.coeff) = _
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      simp only [map_smul, smul_eq_mul, coeffAt, LinearMap.comp_apply, Finsupp.lapply_apply]
      rfl
    refine ⟨fun w hw => ?_, fun w => ?_⟩
    · rw [hCoeff]
      apply Finset.sum_eq_zero
      intro v hv
      have hvn : v.length - 1 = n := by rw [hSupport v hv]; omega
      rw [(hg v).1 w (by rwa [hvn]), mul_zero]
    · rw [hCoeff]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
      intro v _
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) ((hg v).2 w)).trans (hBound v)
  obtain ⟨haLength, haBound⟩ := hSum a ha
  obtain ⟨hbLength, hbBound⟩ := hSum b hb
  refine ⟨left p.coeff, right p.coeff, haLength, hbLength, fun w => ⟨haBound w, hbBound w⟩, ?_⟩
  simpa only [hTrace, map_zero, sub_zero, commutator] using hid p

end Splitting

end Langlands.CyclicWords
