import Langlands.LinearAlgebra.CartanE6RootCoordinates
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Root counts for standard parabolics in type E6 -/

noncomputable section

namespace Langlands.CartanE6Root

open RootReflectionCoefficients
open scoped BigOperators

/-- The integral coefficient vectors of the positive and negative E6 roots. -/
def signedCoefficients (r : Bool × Fin 36) : Fin 6 → ℤ :=
  if r.1 then positiveCoefficients r.2 else -positiveCoefficients r.2

private theorem positiveCoefficients_injective : Function.Injective positiveCoefficients := by
  have h : ∀ i j : Fin 36, positiveCoefficients i = positiveCoefficients j → i = j := by
    decide
  exact h

private theorem positive_ne_negative : ∀ i j : Fin 36,
    positiveCoefficients i ≠ -positiveCoefficients j := by decide

private theorem signedCoefficients_injective : Function.Injective signedCoefficients := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  cases s <;> cases t <;> simp only [signedCoefficients, Bool.false_eq_true,
    ite_false, ite_true, neg_inj] at h
  · exact congrArg (Prod.mk false) (positiveCoefficients_injective h)
  · exact (positive_ne_negative b a h.symm).elim
  · exact (positive_ne_negative a b h).elim
  · exact congrArg (Prod.mk true) (positiveCoefficients_injective h)

section RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) [Finite J] [P.IsReduced] (b : P.Base) (e : b.support ≃ Fin 6)

/-- The signed enumeration is bijective on the roots of every actual based
finite reduced datum with the E6 Cartan matrix in the supplied numbering. -/
theorem exists_signedRootEquiv
    (hE : ∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.E 6 i j) :
    let a : Fin 6 → J := fun i => (e.symm i).val
    ∃ f : (Bool × Fin 36) ≃ J, ∀ p, P.root (f p) = combination P a (signedCoefficients p) := by
  classical
  let a : Fin 6 → J := fun i => (e.symm i).val
  change ∃ f : (Bool × Fin 36) ≃ J, ∀ p, P.root (f p) = combination P a (signedCoefficients p)
  have hneg (x : Fin 6 → ℤ) : combination P a (-x) = -combination P a x := by
    simp only [combination, Pi.neg_apply, neg_zsmul, Finset.sum_neg_distrib]
  have hex (p : Bool × Fin 36) : IsRoot P a (signedCoefficients p) := by
    rcases p with ⟨s, r⟩
    obtain ⟨j, hj⟩ := isRoot_positiveCoefficients P a hE r
    cases s
    · refine ⟨P.reflectionPerm j j, ?_⟩
      rw [P.root_reflectionPerm, P.reflection_apply_self, hj]
      exact (hneg (positiveCoefficients r)).symm
    · exact ⟨j, hj⟩
  choose f hf using hex
  have hli : LinearIndependent ℤ (fun j => P.root (a j)) :=
    b.linearIndepOn_root.comp e.symm e.symm.injective
  have hinj : Function.Injective f := by
    intro x y hxy
    have hw := (hf x).symm.trans ((congrArg P.root hxy).trans (hf y))
    apply signedCoefficients_injective
    funext i
    exact Fintype.linearIndependent_iffₛ.mp hli _ _ hw i
  have hsurj : Function.Surjective f := by
    intro r
    obtain ⟨i, h | h⟩ := exists_signedCoefficients P b e hE r
    · refine ⟨(true, i), P.root.injective ((hf (true, i)).trans h.symm)⟩
    · refine ⟨(false, i), P.root.injective ?_⟩
      exact (hf (false, i)).trans ((hneg _).trans h.symm)
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end RootDatum

/-- Number of negative roots whose support meets the omitted simple vertices. -/
def parabolicCodimension (s : Finset (Fin 6)) : ℕ :=
  (Finset.univ.filter fun r : Bool × Fin 36 => (∑ i ∈ s, signedCoefficients r i) < 0).card

/-- The counts for the two long-arm endpoints, the short-arm endpoint, and the
short-arm endpoint together with the central vertex. -/
def ParabolicCodimensionCountsStatement : Prop :=
  parabolicCodimension {0} = 16 ∧ parabolicCodimension {5} = 16 ∧
    parabolicCodimension {1} = 21 ∧ parabolicCodimension {1, 3} = 30

theorem parabolicCodimensionCounts : ParabolicCodimensionCountsStatement := by
  unfold ParabolicCodimensionCountsStatement
  decide

end Langlands.CartanE6Root
