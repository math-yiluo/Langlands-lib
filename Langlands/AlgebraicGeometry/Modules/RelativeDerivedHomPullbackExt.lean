import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullbackSingle

/-! # Singleton pullback and the Ext-defined sheaf map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic DerivedSectionsHomComparison
open AbelianSheafCohomologyPullback AbelianSheafDerivedSections

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option autoImplicit false

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The actual pushforward image of a singleton complex, after forgetting scalars. -/
def relativePushforwardSingleDerivedIso (f : Y ⟶ X) (N : Y.left.Modules) :
    DerivedCategory.Q.obj (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.left.Modules 0).obj N))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N)) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pushforward f.left ⋙ toAbSheaf X.left) (.up ℤ) 0).app N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))).symm

lemma relativePushforwardSingleDerivedIso_inv (f : Y ⟶ X) (N : Y.left.Modules) :
    (singleComplexDerivedIso.{u+1} (toAbSheaf X.left)
      ((Scheme.Modules.pushforward f.left).obj N)).inv ≫
      DerivedCategory.Q.map (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).map
        (((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N).hom)) =
    (relativePushforwardSingleDerivedIso f N).inv := by
  simp only [singleComplexDerivedIso, relativePushforwardSingleDerivedIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, Category.id_comp]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  change (HomologicalComplex.singleMapHomologicalComplex (toAbSheaf X.left)
      (.up ℤ) 0).inv.app ((Scheme.Modules.pushforward f.left).obj N) ≫ _ = _
  rw [HomologicalComplex.singleMapHomologicalComplex_comp_inv_app]
  congr 1
  congr 1
  change (CochainComplex.Plus.ι _).map
    ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N) = _
  simp only [DerivedPlus.singlePlusMapIso, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.symm_hom, Iso.app_inv]

lemma relativePullbackCounit_single (f : Y ⟶ X) (N : Y.left.Modules) :
    (HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base) (.up ℤ) 0).inv.app
        ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N)) ≫
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pushforward f.left ⋙ toAbSheaf X.left) (.up ℤ) 0).inv.app N) ≫
      relativePullbackCounit f ((CochainComplex.singleFunctor Y.left.Modules 0).obj N) =
    (CochainComplex.singleFunctor _ 0).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          f.left.base).counit.app ((toAbSheaf Y.left).obj N)) ≫
      (HomologicalComplex.singleMapHomologicalComplex (toAbSheaf Y.left)
        (.up ℤ) 0).inv.app N := by
  apply HomologicalComplex.from_single_hom_ext
  simp [relativePullbackCounit, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.single]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

lemma relativePullbackCounit_single_derived (f : Y ⟶ X) (N : Y.left.Modules) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategory.map
        (relativePushforwardSingleDerivedIso f N).inv ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategoryFactors.hom.app
        (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor Y.left.Modules 0).obj N))) ≫
      DerivedCategory.Q.map
        (relativePullbackCounit f ((CochainComplex.singleFunctor Y.left.Modules 0).obj N)) =
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).mapDerivedCategorySingleFunctor
        0).hom.app ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          f.left.base).counit.app ((toAbSheaf Y.left).obj N)) ≫
      (singleComplexDerivedIso.{u+1} (toAbSheaf Y.left) N).inv := by
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base
  let A := (toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N)
  let t := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.pushforward f.left ⋙ toAbSheaf X.left) (.up ℤ) 0).inv.app N
  have h := congrArg DerivedCategory.Q.map (relativePullbackCounit_single f N)
  simp only [Functor.map_comp] at h
  have hf := P.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app A
  have hn := P.mapDerivedCategoryFactors_hom_naturality t
  simp only [Functor.mapCochainComplexSingleFunctor] at hf
  rw [← hf, Category.assoc] at h
  erw [← reassoc_of% hn] at h
  apply (cancel_epi ((P.mapDerivedCategorySingleFunctor 0).inv.app A)).1
  change (P.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      P.mapDerivedCategory.map (DerivedCategory.Q.map t) ≫
      P.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map _ =
    (P.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app A ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map _) ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        (toAbSheaf Y.left) (.up ℤ) 0).inv.app N)
  simp only [Iso.inv_hom_id_app_assoc]
  exact h

lemma relativeComplexHomPullback_single (f : Y ⟶ X) (N : Y.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj
      ((Scheme.Modules.pushforward f.left).obj N)) n) :
    (relativeComplexHomPullback f (n : ℤ)).app
        ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N)
        (x.hom ≫ (relativePushforwardSingleDerivedIso f N).inv⟦(n : ℤ)⟧') =
      (pushforwardMap f.left.base
        (𝟙 ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))) n x).hom ≫
        (singleComplexDerivedIso.{u+1} (toAbSheaf Y.left) N).inv⟦(n : ℤ)⟧' := by
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base
  have hAdj :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        f.left.base).homEquiv
          ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))
          ((toAbSheaf Y.left).obj N)).symm
        (𝟙 ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        f.left.base).counit.app ((toAbSheaf Y.left).obj N) := by
    exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      f.left.base).homEquiv_symm_id _
  change (DerivedCategory.singleFunctor _ 0).map
      ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ))) ≫
    (P.mapDerivedCategorySingleFunctor 0).inv.app (constantIntegers X.left.toTopCat) ≫
    ShiftedHom.map (x.hom ≫ (relativePushforwardSingleDerivedIso f N).inv⟦(n : ℤ)⟧')
      P.mapDerivedCategory ≫
    (P.mapDerivedCategoryFactors.hom.app _)⟦(n : ℤ)⟧' ≫
    (DerivedCategory.Q.map (relativePullbackCounit f
      ((CochainComplex.singleFunctor Y.left.Modules 0).obj N)))⟦(n : ℤ)⟧' = _
  erw [← ShiftedHom.comp_mk₀ x.hom (0 : ℤ) rfl
      (relativePushforwardSingleDerivedIso f N).inv,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀]
  simp only [pushforwardMap, hAdj, pullbackMap,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, CategoryTheory.Abelian.Ext.comp_hom,
    CategoryTheory.Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    CategoryTheory.Abelian.Ext.mapExactFunctor_hom]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [relativePullbackCounit_single_derived]
  rfl

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
