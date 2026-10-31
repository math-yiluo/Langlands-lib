import Mathlib
import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd

/-! # Geometric connectedness from the generic fibre for smooth proper morphisms

A smooth proper morphism to the spectrum of a noetherian integrally closed domain is
geometrically connected as soon as its generic fibre is.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Let `R` be a noetherian integrally closed domain with fraction field `K`, and let
`f : X ⟶ Spec R` be smooth and proper. If the generic fibre `X ×_R K ⟶ Spec K` is
geometrically connected, then `f` is geometrically connected. -/
theorem geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Smooth f]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    GeometricallyConnected f := by
  have hiso : IsIso (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop :=
    fieldSmoothProperConnectedGlobalFunctions K _ _ inferInstance inferInstance inferInstance
  exact AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd
    K f (ConcreteCategory.bijective_of_isIso _)

end Langlands.AlgebraicGeometry.NoetherianApproximation
