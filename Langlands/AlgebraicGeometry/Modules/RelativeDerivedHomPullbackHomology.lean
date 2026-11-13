import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullbackCompatibility

/-! # Pullback compatibility on cohomology of sections complexes -/

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

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

@[reassoc]
lemma relativeSectionsHomologyIso_pullback (f : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) (n : ℤ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        (DerivedCategory.Plus.Q.map (DerivedSections.pullbackSectionsComplexIso f K).hom)) ≫
      (sectionsHomologyIso (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) K n).hom =
    (sectionsHomologyIso (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom)
      ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) n).hom ≫
      HomologicalComplex.homologyMap
        (EquivariantComposite.homComplexMap
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base)
          ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)))
          (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
            (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj))) n ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (constantIntegers Y.left.toTopCat))).mapHomologicalComplex
          (.up ℤ)).map (relativePullbackCounit f K.obj)) n := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let a := (DerivedSections.pullbackSectionsComplexIso f K).hom
  have h₁ := congrArg G.map
    (DerivedPlusSource.localizedHomologyIso_hom_naturality a n)
  have h₂ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) n).map a.hom) G
  have h₃ := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) n).map
    (relativeSectionsComplexIso_pullback f K)
  simp only [Functor.map_comp] at h₁ h₃
  change G.map (HomologicalComplex.homologyMap a.hom n) ≫
      (((((DerivedSections.relativeGlobalSections Y.hom).mapHomologicalComplex (.up ℤ)).obj
        K.obj).sc n).mapHomologyIso G).inv =
    (((((DerivedSections.relativeGlobalSections X.hom).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)).sc n).mapHomologyIso G).inv ≫
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map a.hom) n at h₂
  simp only [sectionsHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  erw [reassoc_of% h₁, reassoc_of% h₂, ← h₃]
  rfl

/-- Cohomology of the actual pushforward/sections comparison on complexes. -/
def relativeComplexSectionsPullback (f : Y ⟶ X) (n : ℤ) :
    (Scheme.Modules.pushforward f.left).mapCochainComplexPlus ⋙
      (DerivedSections.relativeGlobalSections X.hom).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙
          sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n ⟶
    (DerivedSections.relativeGlobalSections Y.hom).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙
        sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n :=
  whiskerRight
    (whiskerRight (DerivedSections.relativePushforwardSectionsComplexIso f).hom
      DerivedCategory.Plus.Q)
    (sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n)

@[reassoc]
lemma relativeComplexComparison_pullback (f : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) (n : ℤ) :
    (complexComparison.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) n).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) ≫
      (relativeComplexHomPullback f n).app K =
    (relativeComplexSectionsPullback f n).app K ≫
      (complexComparison.{u+1} (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) n).app K := by
  ext x
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base
  let KX := ((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
    (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)
  let s := (sectionsHomologyIso (DerivedSections.relativeGlobalSections X.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
    (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom)
    ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) n).hom x.down
  have h := ConcreteCategory.congr_hom (relativeSectionsHomologyIso_pullback f K n) x.down
  have hF := EquivariantComposite.homologyDerivedMap_map P
    ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) KX n s
  have hN := EquivariantComposite.homologyDerivedMap_naturality
    (constantIntegers Y.left.toTopCat) (relativePullbackCounit f K.obj) n
    (HomologicalComplex.homologyMap
      (EquivariantComposite.homComplexMap P
        ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) KX) n s)
  change (sectionsHomologyIso (DerivedSections.relativeGlobalSections Y.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
      (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) K n).hom
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
          (DerivedCategory.Plus.Q.map (DerivedSections.pullbackSectionsComplexIso f K).hom))
        x.down) =
    HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op (constantIntegers Y.left.toTopCat))).mapHomologicalComplex
        (.up ℤ)).map (relativePullbackCounit f K.obj)) n
      (HomologicalComplex.homologyMap
        (EquivariantComposite.homComplexMap P
          ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) KX) n s) at h
  change (DerivedCategory.singleFunctor _ 0).map
      ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) ≫
    (P.mapDerivedCategorySingleFunctor 0).inv.app (constantIntegers X.left.toTopCat) ≫
    ShiftedHom.map (EquivariantComposite.homologyDerivedMap
      (constantIntegers X.left.toTopCat) KX n s) P.mapDerivedCategory ≫
    (P.mapDerivedCategoryFactors.hom.app KX)⟦n⟧' ≫
    (DerivedCategory.Q.map (relativePullbackCounit f K.obj))⟦n⟧' =
    EquivariantComposite.homologyDerivedMap (constantIntegers Y.left.toTopCat)
      (((toAbSheaf Y.left).mapHomologicalComplex (.up ℤ)).obj K.obj) n
      ((sectionsHomologyIso (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) K n).hom
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
            (DerivedCategory.Plus.Q.map (DerivedSections.pullbackSectionsComplexIso f K).hom))
          x.down))
  rw [h, hN]
  erw [hF]
  simp only [Category.assoc]
  rfl

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
