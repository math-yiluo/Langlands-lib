import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullbackHomology

/-! # Right-derived relative sections and pullback compatibility -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic
open AbelianSheafCohomologyPullback AbelianSheafDerivedSections
open DerivedSectionsHomComparison

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
set_option autoImplicit false

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- Cohomology of the canonical comparison from pushforward-derived sections. -/
def relativeDerivedComplexSectionsPullback (f : Y ⟶ X) (n : ℤ) :
    (Scheme.Modules.pushforward f.left).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙
        derivedSections.{u+1} (DerivedSections.relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n ⟶
    DerivedCategory.Plus.Q ⋙
      derivedSections.{u+1} (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n :=
  whiskerRight (DerivedSections.pushforwardDerivedSectionsComparison f)
    (sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n)

@[reassoc]
lemma relativeDerivedComplexSectionsPullback_fac (f : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) (n : ℤ) :
    (sectionsUnit.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) ≫
      (relativeDerivedComplexSectionsPullback f n).app K =
    (relativeComplexSectionsPullback f n).app K ≫
      (sectionsUnit.{u+1} (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).app K := by
  let H := sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp, DerivedSections.pushforwardDerivedSectionsComparison_fac]
  rfl

lemma relativeComparisonOnComplex_pullback (f : Y ⟶ X) (n : ℤ) :
    (whiskerLeft (Scheme.Modules.pushforward f.left).mapCochainComplexPlus
      (comparisonOnComplex.{u+1} (DerivedSections.relativeGlobalSections X.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
        (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) n) :
      (Scheme.Modules.pushforward f.left).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙
        derivedSections.{u+1} (DerivedSections.relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n ⟶
      (Scheme.Modules.pushforward f.left).mapCochainComplexPlus ⋙
        complexHom.{u+1} (toAbSheaf X.left) (constantIntegers X.left.toTopCat) n) ≫
      relativeComplexHomPullback f n =
    relativeDerivedComplexSectionsPullback f n ≫
      comparisonOnComplex.{u+1} (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) n := by
  apply (cancel_mono (derivedHomFactors.{u+1} (toAbSheaf Y.left)
    (constantIntegers Y.left.toTopCat) n).inv).1
  apply DerivedPlus.natTrans_ext_on_injective_complexes
  intro I
  let K := (InjectiveObject.ι Y.left.Modules).mapCochainComplexPlus.obj I
  have := DerivedSections.isIso_unit_pushforward_injective_complex f I
  have hU : IsIso ((sectionsUnit.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K)) := by
    dsimp only [sectionsUnit, whiskerRight_app]
    infer_instance
  have : Epi ((sectionsUnit.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K)) :=
    @IsIso.epi_of_iso _ _ _ _ _ hU
  have h : (comparisonOnComplex.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) ≫
      (relativeComplexHomPullback f n).app K =
    (relativeDerivedComplexSectionsPullback f n).app K ≫
      (comparisonOnComplex.{u+1} (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) n).app K := by
    apply (cancel_epi ((sectionsUnit.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K))).1
    rw [← Category.assoc, unit_comparisonOnComplex_app]
    rw [relativeDerivedComplexSectionsPullback_fac_assoc,
      unit_comparisonOnComplex_app]
    exact relativeComplexComparison_pullback f K n
  simpa only [NatTrans.comp_app, whiskerLeft_app] using
    congrArg (fun a => a ≫ (derivedHomFactors.{u+1} (toAbSheaf Y.left)
      (constantIntegers Y.left.toTopCat) n).inv.app K) h

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
