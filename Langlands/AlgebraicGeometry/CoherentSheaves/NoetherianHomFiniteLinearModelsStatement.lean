import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.FiniteLinearModels
import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite linear models for proper Hom over a noetherian affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- The ordinary module Hom presheaf of a proper finitely presented scheme over
a noetherian affine base has finite homogeneous linear models locally on the
base, provided the target module is flat over the base. -/
def NoetherianHomFiniteLinearModelsStatement : Prop :=
  ∀ (R : CommRingCat.{u}), IsNoetherianRing R →
    ∀ (Y : Scheme.{u}) (p : Y ⟶ Spec R),
      IsProper p → LocallyOfFinitePresentation p →
        ∀ (M N : Y.Modules),
          M.IsFinitePresentation → N.IsFinitePresentation →
            Modules.IsFlatOver p N →
              FiniteLinearEquations.HasLocalModels
                (intrinsicModuleHomPresheaf p M N)

end Langlands.AlgebraicGeometry.CoherentSheaves
