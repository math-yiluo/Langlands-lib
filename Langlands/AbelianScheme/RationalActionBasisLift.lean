import Langlands.AbelianScheme.BaseChangeSurjectiveRigidity
import Langlands.AbelianScheme.RationalAlgebraAction
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Lifting a rational action from lifts of integral multiples of a basis -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

/-- Surjective base change identifies the rational endomorphism algebra
with its image in the rational endomorphism algebra after base change. -/
def rationalBaseChangeEndRangeEquiv {S T : Scheme.{u}} (b : T ⟶ S) [Surjective b]
    (B : AbelianScheme S) : End0 B ≃ₐ[ℚ] (rationalBaseChangeEnd b B).range := by
  apply AlgEquiv.ofInjective (rationalBaseChangeEnd b B)
  intro x y h
  apply CategoryTheory.End.ext
  exact rationalBaseChangeIsFaithful_of_surjective b B B
    (congrArg CategoryTheory.End.asHom h)

/-- The rational action on the reduction lifts if integral multiples of the
action of basis elements are restrictions of integral endomorphisms. -/
theorem exists_rationalAction_of_basis_lifts
    {S T : Scheme.{u}} (b : T ⟶ S) [Surjective b] (B : AbelianScheme S)
    {A : Type v} [Ring A] [Algebra ℚ A] {ι : Type w} (basis : Module.Basis ι ℚ A)
    (ρ : A →ₐ[ℚ] End0 ((baseChange b).obj B)) (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (f : ι → (B ⟶ B))
    (hf : ∀ i, homToHom0 ((baseChange b).map (f i)) = m i • (ρ (basis i)).asHom) :
    ∃ σ : A →ₐ[ℚ] End0 B, (rationalBaseChangeEnd b B).comp σ = ρ := by
  let j := rationalBaseChangeEnd b B
  have hb (i : ι) : ρ (basis i) ∈ j.range := by
    have hbase : (m i : ℚ) • ρ (basis i) ∈ j.range := by
      refine ⟨Rationalization.ofEnd B (CategoryTheory.End.of (f i)), ?_⟩
      apply CategoryTheory.End.ext
      change rationalBaseChangeHom b (Rationalization.ofHom (f i)) =
        (m i : ℚ) • (ρ (basis i)).asHom
      rw [rationalBaseChangeHom_ofHom, Int.cast_smul_eq_zsmul]
      exact hf i
    have hnonzero : (m i : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (hm i)
    change ρ (basis i) ∈ j.range.toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hnonzero, one_smul] using
      j.range.toSubmodule.smul_mem (m i : ℚ)⁻¹ hbase
  have hr : ∀ a : A, ρ a ∈ j.range := by
    have hspan : Submodule.span ℚ (Set.range basis) ≤
        j.range.toSubmodule.comap ρ.toLinearMap :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
    rw [basis.span_eq] at hspan
    intro a
    exact hspan (Submodule.mem_top (R := ℚ) (M := A) (x := a))
  let e := rationalBaseChangeEndRangeEquiv b B
  refine ⟨e.symm.toAlgHom.comp (ρ.codRestrict j.range hr), ?_⟩
  apply AlgHom.ext
  intro a
  exact congrArg Subtype.val (e.apply_symm_apply ⟨ρ a, hr a⟩)

end Langlands.AbelianScheme
