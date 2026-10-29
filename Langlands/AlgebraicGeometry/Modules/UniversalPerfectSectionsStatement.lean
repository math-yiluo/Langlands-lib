import Langlands.Cohomology.PerfectModuleComplex
import Langlands.Cohomology.DerivedPlus
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Universal perfect representatives for smooth proper line-bundle sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Actual derived sections of a line bundle on a smooth proper affine-base
family admit one perfect representative computing every affine scalar change. -/
def UniversalPerfectSectionsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R),
    Smooth f → IsProper f →
    ∀ L : Picard.LineBundle X,
      ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
        Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect K ∧
        Nonempty (DerivedCategory.Q.obj K ≅
          DerivedCategory.Plus.ι.obj
            ((Langlands.Cohomology.DerivedPlus.derivedComplex
              (DerivedSections.relativeGlobalSections f)).obj L.obj)) ∧
        ∀ (T : CommRingCat.{u}) (φ : R ⟶ T),
          Nonempty
            (DerivedCategory.Q.obj
                ((Langlands.Cohomology.ModuleComplex.baseChange φ.hom).obj K) ≅
              DerivedCategory.Plus.ι.obj
                ((Langlands.Cohomology.DerivedPlus.derivedComplex
                  (DerivedSections.relativeGlobalSections
                    (pullback.snd f (Spec.map φ)))).obj
                    ((Scheme.Modules.pullback
                      (pullback.fst f (Spec.map φ))).obj L.obj)))

end Langlands.AlgebraicGeometry.Modules
