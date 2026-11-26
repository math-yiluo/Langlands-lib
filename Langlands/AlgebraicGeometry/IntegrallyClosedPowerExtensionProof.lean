import Langlands.AlgebraicGeometry.IntegrallyClosedPowerExtensionStatement
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Extending sections whose power extends -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Milne's Lemma 22.23, using the function field of the integral affine scheme. -/
theorem integrallyClosedPowerExtension : IntegrallyClosedPowerExtensionStatement.{u} := by
  intro X _ _ hClosed U hU f d hd hf
  obtain ⟨x, hx⟩ := hU
  obtain ⟨g, hg⟩ := hf
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  have germRestrict (s : Γ(X, ⊤)) :
      X.germToFunctionField U (X.presheaf.map (homOfLE le_top).op s) =
        algebraMap Γ(X, ⊤) X.functionField s :=
    X.presheaf.germ_res_apply (homOfLE le_top) _ _ s
  have powerIntegral : IsIntegral Γ(X, ⊤) ((X.germToFunctionField U f) ^ d) := by
    rw [← map_pow, ← hg, germRestrict]
    exact isIntegral_algebraMap
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hd powerIntegral
  exact ⟨h, X.germToFunctionField_injective U ((germRestrict h).trans hh)⟩

end Langlands.AlgebraicGeometry
