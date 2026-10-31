import Langlands.Cohomology.PerfectModuleComplex
import Langlands.Cohomology.DerivedPlus
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # A fixed universal perfect representative of actual derived sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- A fixed strictly perfect complex represents actual derived relative
sections both over the original ring and after every affine scalar change. -/
def IsUniversalPerfectSectionsRepresentative
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (M : X.Modules) (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect K ∧
    Nonempty (DerivedCategory.Q.obj K ≅
      DerivedCategory.Plus.ι.obj
        ((Langlands.Cohomology.DerivedPlus.derivedComplex
          (DerivedSections.relativeGlobalSections f)).obj M)) ∧
    ∀ (T : CommRingCat.{u}) (φ : R ⟶ T),
      Nonempty
        (DerivedCategory.Q.obj
            ((Langlands.Cohomology.ModuleComplex.baseChange φ.hom).obj K) ≅
          DerivedCategory.Plus.ι.obj
            ((Langlands.Cohomology.DerivedPlus.derivedComplex
              (DerivedSections.relativeGlobalSections
                (pullback.snd f (Spec.map φ)))).obj
                ((Scheme.Modules.pullback
                  (pullback.fst f (Spec.map φ))).obj M)))

end Langlands.AlgebraicGeometry.Modules
