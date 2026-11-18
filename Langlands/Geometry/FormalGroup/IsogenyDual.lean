import Langlands.Geometry.FormalGroup.PointFactorization
import Langlands.Geometry.FormalGroup.IsogenyKernelTorsion
import Langlands.Geometry.FormalGroup.DualIsogenyKernel

/-! # Integral scalar-power dual isogenies -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw.Hom
open CategoryTheory
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

/-- Every isogeny of scalar-divisible formal modules has integral isogeny
duals at every sufficiently large scalar-power exponent. -/
theorem IsIsogeny.exists_dual
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {f : Hom M N} (hf : f.IsIsogeny) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∃ g : Hom N M,
      g.IsIsogeny ∧ g.comp f = M.scalarHom (π ^ j) ∧
        f.comp g = N.scalarHom (π ^ j) := by
  obtain ⟨j₀, hj₀⟩ := hf.exists_eventually_pow_kills_kernel hM
  refine ⟨j₀, ?_⟩
  intro j hj
  obtain ⟨g, hgf⟩ := exists_comp_eq (h := M.scalarHom (π ^ j)) hf.1 (by
    intro A x hx
    rw [scalarHom_onAlgebraPoints]
    exact hj₀ j hj A ⟨x, hx⟩)
  have hfg : f.comp g = N.scalarHom (π ^ j) :=
    hf.1.comp_right_cancel (by
      rw [comp_assoc, hgf, Hom.comp_scalarHom])
  exact ⟨g, ⟨isFppfLocallySurjective_of_comp_eq_scalarHom hM f g j hgf,
    hasFiniteLocallyFreeKernel_of_comp_eq_scalarHom hM hN hf hgf hfg⟩, hgf, hfg⟩

end Langlands.FormalGroup.ModuleLaw.Hom
