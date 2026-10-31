import Langlands.AlgebraicGeometry.Modules.SchemeIsoDerivedSectionsStatement
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology
import Langlands.AlgebraicGeometry.Modules.DerivedPushforwardComparison

/-! # Scheme isomorphism invariance of actual derived sections: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

namespace DerivedSections

/-- Actual derived relative sections are invariant under scheme isomorphisms,
naturally in the coefficient module. -/
def relativeDerivedSectionsPullbackIso {X Y : Scheme.{u}} (e : X ≅ Y)
    {R : CommRingCat.{u}} (g : Y ⟶ Spec R) :
    Scheme.Modules.pullback e.hom ⋙
        (DerivedPlus.derivedComplex (relativeGlobalSections (e.hom ≫ g)) ⋙
          DerivedCategory.Plus.ι) ≅
      DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
        DerivedCategory.Plus.ι := by
  letI : (Scheme.Modules.pushforward e.hom).IsEquivalence :=
    (pushforwardEquivalence e).isEquivalence_functor
  let hM : ∀ M : Y.Modules, ∀ q : ℕ,
      IsZero ((higherDirectImage e.hom (q + 1)).obj
        ((Scheme.Modules.pullback e.hom).obj M)) :=
    fun M q => closedImmersionHigherDirectImageVanishing X Y e.hom inferInstance _ q
  let D := DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
    DerivedCategory.Plus.ι
  let β :
      Scheme.Modules.pullback e.hom ⋙
          (DerivedPlus.derivedComplex (relativeGlobalSections (e.hom ≫ g)) ⋙
            DerivedCategory.Plus.ι) ≅
        (Scheme.Modules.pullback e.hom ⋙ Scheme.Modules.pushforward e.hom) ⋙ D :=
    NatIso.ofComponents
      (fun M => derivedPushforwardComparisonIso e.hom g
        ((Scheme.Modules.pullback e.hom).obj M) (hM M))
      (fun φ => derivedPushforwardComparison_naturality e.hom g
        ((Scheme.Modules.pullback e.hom).map φ) (hM _) (hM _))
  exact β ≪≫
    Functor.isoWhiskerRight
      (asIso (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit).symm D ≪≫
      Functor.leftUnitor D

end DerivedSections

/-- The natural isomorphism proves the published transport proposition. -/
theorem schemeIsoDerivedSections : SchemeIsoDerivedSectionsStatement.{u} := by
  intro R X Y e g
  exact ⟨DerivedSections.relativeDerivedSectionsPullbackIso e g⟩

end Langlands.AlgebraicGeometry.Modules
