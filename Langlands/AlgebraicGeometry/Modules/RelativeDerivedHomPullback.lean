import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomComparison

/-! # Pullback and the relative derived Hom comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic
open AbelianSheafCohomologyPullback AbelianSheafDerivedSections

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

lemma homGlobalSectionsIso_pullback_counit (f : Y ⟶ X)
    (B : TopCat.Sheaf AddCommGrpCat.{u} Y.left.toTopCat)
    (b : constantIntegers X.left.toTopCat ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.left.base).obj B) :
    (homGlobalSectionsIso Y.left.toTopCat).hom.app B
      ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).map b ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          f.left.base).counit.app B) =
    (homGlobalSectionsIso X.left.toTopCat).hom.app
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.left.base).obj B) b := by
  let adjX := constantSheafAdj (Opens.grothendieckTopology X.left.toTopCat)
    AddCommGrpCat.{u} (isTerminalTop (α := TopologicalSpace.Opens X.left.toTopCat))
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y.left.toTopCat)
    AddCommGrpCat.{u} (isTerminalTop (α := TopologicalSpace.Opens Y.left.toTopCat))
  let adjP := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.left.base
  let a := (AddCommGrpCat.of (ULift.{u} ℤ))
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (adjY.homEquiv a B ((constantPullbackIso f.left.base).inv.app a ≫
        (adjP.homEquiv _ B).symm b)) =
    AddCommGrpCat.uliftZMultiplesAddEquiv _ (adjX.homEquiv a _ b)
  congr 1
  have h := Adjunction.unit_leftAdjointUniq_hom_app (adjX.comp adjP) adjY a
  rw [Adjunction.homEquiv_unit]
  rw [← h]
  simp only [Functor.map_comp, Category.assoc]
  change (adjX.comp adjP).unit.app a ≫
      (AbelianSheafDerivedSections.globalSections Y.left.toTopCat).map
        ((constantPullbackIso f.left.base).hom.app a) ≫
      (AbelianSheafDerivedSections.globalSections Y.left.toTopCat).map
        ((constantPullbackIso f.left.base).inv.app a) ≫
      (AbelianSheafDerivedSections.globalSections Y.left.toTopCat).map
        ((adjP.homEquiv _ B).symm b) = _
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  change (adjX.comp adjP).homEquiv a B ((adjP.homEquiv _ B).symm b) = _
  rw [Adjunction.comp_homEquiv]
  exact congrArg (adjX.homEquiv a _) ((adjP.homEquiv _ B).apply_symm_apply b)

/-- The actual inverse-image/direct-image counit on an underlying module complex. -/
def relativePullbackCounit (f : Y ⟶ X) (K : CochainComplex Y.left.Modules ℤ) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapHomologicalComplex (.up ℤ)).obj
      (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K)) ⟶
      ((toAbSheaf Y.left).mapHomologicalComplex (.up ℤ)).obj K where
  f i := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f.left.base).counit.app ((toAbSheaf Y.left).obj (K.X i))
  comm' i j _ := by
    exact ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      f.left.base).counit.naturality ((toAbSheaf Y.left).map (K.d i j))).symm

@[reassoc]
lemma relativePullbackCounit_naturality (f : Y ⟶ X)
    {K L : CochainComplex Y.left.Modules ℤ} (a : K ⟶ L) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapHomologicalComplex (.up ℤ)).map
      (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).map
        (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).map a)) ≫
      relativePullbackCounit f L =
    relativePullbackCounit f K ≫
      ((toAbSheaf Y.left).mapHomologicalComplex (.up ℤ)).map a := by
  apply HomologicalComplex.hom_ext
  intro i
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f.left.base).counit.naturality ((toAbSheaf Y.left).map (a.f i))

/-- The pullback/counit action on localized Hom of actual module complexes. -/
def relativeComplexHomPullback (f : Y ⟶ X) (n : ℤ) :
    (Scheme.Modules.pushforward f.left).mapCochainComplexPlus ⋙
      DerivedSectionsHomComparison.complexHom.{u+1} (toAbSheaf X.left)
        (constantIntegers X.left.toTopCat) n ⟶
    DerivedSectionsHomComparison.complexHom.{u+1} (toAbSheaf Y.left)
      (constantIntegers Y.left.toTopCat) n where
  app K := AddCommGrpCat.ofHom
    { toFun := fun z =>
        (DerivedCategory.singleFunctor _ 0).map
            ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) ≫
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategorySingleFunctor
            0).inv.app (constantIntegers X.left.toTopCat) ≫
          ShiftedHom.map z (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategory ≫
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategoryFactors.hom.app
            (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
              (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)))⟦n⟧' ≫
          (DerivedCategory.Q.map (relativePullbackCounit f K.obj))⟦n⟧'
      map_zero' := by simp
      map_add' := by
        intro z z'
        let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base
        change (DerivedCategory.singleFunctor _ 0).obj (constantIntegers X.left.toTopCat) ⟶
          (DerivedCategory.Q.obj
            (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
              (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)))⟦n⟧
          at z z'
        have h := ShiftedHom.map_add z z' P.mapDerivedCategory
        rw [h]
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rfl }

  naturality K L a := by
    ext z
    let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base
    let aX := ((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).map
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).map a.hom)
    let aY := ((toAbSheaf Y.left).mapHomologicalComplex (.up ℤ)).map a.hom
    let s := (DerivedCategory.singleFunctor _ 0).map
      ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)))
    let t := (P.mapDerivedCategorySingleFunctor 0).inv.app (constantIntegers X.left.toTopCat)
    let kX := ((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)
    let lX := ((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj L.obj)
    change s ≫ t ≫ ShiftedHom.map (z ≫ (DerivedCategory.Q.map aX)⟦n⟧')
        P.mapDerivedCategory ≫ (P.mapDerivedCategoryFactors.hom.app lX)⟦n⟧' ≫
        (DerivedCategory.Q.map (relativePullbackCounit f L.obj))⟦n⟧' =
      (s ≫ t ≫ ShiftedHom.map z P.mapDerivedCategory ≫
        (P.mapDerivedCategoryFactors.hom.app kX)⟦n⟧' ≫
        (DerivedCategory.Q.map (relativePullbackCounit f K.obj))⟦n⟧') ≫
        (DerivedCategory.Q.map aY)⟦n⟧'
    erw [← ShiftedHom.comp_mk₀ z (0 : ℤ) rfl (DerivedCategory.Q.map aX),
      ShiftedHom.map_comp, ShiftedHom.map_mk₀,
      ShiftedHom.comp_mk₀]
    have h : P.mapDerivedCategory.map (DerivedCategory.Q.map aX) ≫
        P.mapDerivedCategoryFactors.hom.app lX ≫
          DerivedCategory.Q.map (relativePullbackCounit f L.obj) =
        P.mapDerivedCategoryFactors.hom.app kX ≫
          DerivedCategory.Q.map (relativePullbackCounit f K.obj) ≫ DerivedCategory.Q.map aY := by
      erw [P.mapDerivedCategoryFactors_hom_naturality_assoc]
      rw [← DerivedCategory.Q.map_comp, relativePullbackCounit_naturality,
        DerivedCategory.Q.map_comp]
    have hn := congrArg (fun b => b⟦n⟧') h
    simp only [Functor.map_comp] at hn
    simp only [Category.assoc]
    erw [hn]

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
