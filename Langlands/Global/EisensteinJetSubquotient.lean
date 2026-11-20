import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Simple subquotients detected by finitely many coefficient maps -/

noncomputable section

namespace Langlands.Global.EisensteinJet

variable {R J Z Q ι : Type*} [Ring R]
variable [AddCommGroup J] [Module R J] [AddCommGroup Z] [Module R Z]
variable [AddCommGroup Q] [Module R Q]

/-- Descend a specialization to a coefficient image when the specialization
vanishes on the kernel of that coefficient. -/
def coefficientQuotient (c : J →ₗ[R] Z) (q : J →ₗ[R] Q)
    (h : LinearMap.ker c ≤ LinearMap.ker q) :
    LinearMap.range c →ₗ[R] Q :=
  ((LinearMap.ker c).liftQ q h).comp c.quotKerEquivRange.symm.toLinearMap

theorem coefficientQuotient_surjective (c : J →ₗ[R] Z) (q : J →ₗ[R] Q)
    (h : LinearMap.ker c ≤ LinearMap.ker q) (hq : Function.Surjective q) :
    Function.Surjective (coefficientQuotient c q h) := by
  intro y
  obtain ⟨x, rfl⟩ := hq y
  refine ⟨c.rangeRestrict x, ?_⟩
  change (LinearMap.ker c).liftQ q h (c.quotKerEquivRange.symm ⟨c x, _⟩) = q x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- If finitely many coefficient maps detect a simple specialization, it is
a quotient of a submodule of the coefficient space. -/
theorem exists_subquotient_of_coefficients [IsSimpleModule R Q]
    (s : Finset ι) (c : ι → J →ₗ[R] Z) (q : J →ₗ[R] Q)
    (D : Submodule R J) (hq : Function.Surjective (q.comp D.subtype))
    (h : ∀ x ∈ D, (∀ i ∈ s, c i x = 0) → q x = 0) :
    ∃ U : Submodule R Z, ∃ p : U →ₗ[R] Q, Function.Surjective p := by
  classical
  induction s using Finset.induction_on generalizing D with
  | empty =>
      let := IsSimpleModule.nontrivial R Q
      obtain ⟨y, hy⟩ := exists_ne (0 : Q)
      obtain ⟨x, hx⟩ := hq y
      exact (hy (hx.symm.trans (h x x.property (by simp)))).elim
  | @insert i s hi ih =>
      let D₀ := D ⊓ LinearMap.ker (c i)
      let q₀ := q.comp D₀.subtype
      rcases eq_bot_or_eq_top (LinearMap.range q₀) with hbot | htop
      · let c' := (c i).comp D.subtype
        let q' := q.comp D.subtype
        have hker : LinearMap.ker c' ≤ LinearMap.ker q' := by
          intro x hx
          let y : D₀ := ⟨x, x.property, hx⟩
          have hz := LinearMap.congr_fun (LinearMap.range_eq_bot.mp hbot) y
          exact LinearMap.mem_ker.mpr hz
        exact ⟨LinearMap.range c', coefficientQuotient c' q' hker,
          coefficientQuotient_surjective c' q' hker hq⟩
      · refine ih D₀ (LinearMap.range_eq_top.mp htop) ?_
        intro x hx hc
        apply h x hx.1
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hx.2
        · exact hc j hj

end Langlands.Global.EisensteinJet
