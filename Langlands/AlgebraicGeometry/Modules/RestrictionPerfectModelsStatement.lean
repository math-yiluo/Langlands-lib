import Langlands.Cohomology.PerfectModuleComplex
import Langlands.Cohomology.DerivedPlus
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Universal perfect models compatible with closed restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

open Langlands.Cohomology in
/-- Derived sections of a line bundle on a smooth proper family over an affine
base have one bounded finite projective model computing every base change along
any pullback square, and every closed restriction to a smooth closed subscheme
is represented by a chain map of such models compatibly with every base
change. The restriction is the derived image of the adjunction unit into the
direct image of the pulled-back bundle. -/
def RestrictionPerfectModelsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R),
    Smooth f → IsProper f →
    ∀ L : Picard.LineBundle X,
      ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
        ModuleComplex.IsStrictlyPerfect K ∧
        ∃ α : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X)
            (f' : X' ⟶ Spec T), IsPullback p f' f (Spec.map φ) →
            (DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K) ≅
              DerivedCategory.Plus.ι.obj
                ((DerivedPlus.derivedComplex
                  (DerivedSections.relativeGlobalSections f')).obj
                    ((Scheme.Modules.pullback p).obj L.obj))),
          ∀ (Y : Scheme.{u}) (g : Y ⟶ X), IsClosedImmersion g → Smooth (g ≫ f) →
            ∃ K' : CochainComplex (ModuleCat.{u} R) ℤ,
              ModuleComplex.IsStrictlyPerfect K' ∧
              ∃ (ψ : K ⟶ K')
                (β : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u})
                  (p : X' ⟶ X) (f' : X' ⟶ Spec T), IsPullback p f' f (Spec.map φ) →
                  ∀ (Y' : Scheme.{u}) (q : Y' ⟶ Y) (g' : Y' ⟶ X'), IsPullback q g' g p →
                  (DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K') ≅
                    DerivedCategory.Plus.ι.obj
                      ((DerivedPlus.derivedComplex
                        (DerivedSections.relativeGlobalSections f')).obj
                          ((Scheme.Modules.pushforward g').obj
                            ((Scheme.Modules.pullback g').obj
                              ((Scheme.Modules.pullback p).obj L.obj)))))),
                ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X)
                  (f' : X' ⟶ Spec T) (hX : IsPullback p f' f (Spec.map φ))
                  (Y' : Scheme.{u}) (q : Y' ⟶ Y) (g' : Y' ⟶ X')
                  (hY : IsPullback q g' g p),
                  DerivedCategory.Q.map ((ModuleComplex.baseChange φ.hom).map ψ) ≫
                      (β T φ X' p f' hX Y' q g' hY).hom =
                    (α T φ X' p f' hX).hom ≫
                      DerivedCategory.Plus.ι.map
                        ((DerivedPlus.derivedComplex
                          (DerivedSections.relativeGlobalSections f')).map
                          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
                            ((Scheme.Modules.pullback p).obj L.obj)))

end Langlands.AlgebraicGeometry.Modules
