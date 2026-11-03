import Langlands.AlgebraicGeometry.CoherentSheaves.NoetherianHomFiniteLinearModelsStatement
import Langlands.AlgebraicGeometry.TensorSectionsHomology

/-! # A universal connective perfect comparison for proper module Hom -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- Proper module Hom over a noetherian affine base is computed by one
universally connective strictly perfect coefficient complex. -/
def NoetherianHomPerfectComparisonStatement : Prop :=
  ∀ (R : CommRingCat.{u}), IsNoetherianRing R →
    ∀ (Y : Scheme.{u}) (p : Y ⟶ Spec R),
      IsProper p → LocallyOfFinitePresentation p →
        ∀ (M N : Y.Modules),
          M.IsFinitePresentation → N.IsFinitePresentation →
            Modules.IsFlatOver p N →
              ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
                Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect K ∧
                (∀ (S : CommRingCat.{u}) (φ : R ⟶ S) (n : ℤ), n < 0 →
                  Limits.IsZero
                    (((Langlands.Cohomology.ModuleComplex.baseChange φ.hom).obj K).homology n)) ∧
                Nonempty (intrinsicModuleHomPresheaf p M N ≅
                  TensorSections.homologyPresheaf K 0)

end Langlands.AlgebraicGeometry.CoherentSheaves
