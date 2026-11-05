import Langlands.Cohomology.ExtRightDerivedNaturality
import Langlands.Cohomology.DerivedPlusSourceLocalization
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackDegreeZeroProof

/-! # Exact-functor Ext maps on actual injective resolutions -/

noncomputable section
universe wC wD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CochainComplex HomComplex
open Langlands.Cohomology Langlands.Cohomology.DerivedComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.ExtResolutionMap

private lemma fromSingleMk_f_zero
    {C : Type*} [Category* C] [Abelian C] {X : C}
    {K : CochainComplex C ℤ} {n : ℤ} (f : X ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) :
    (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n)
      (n + 1) rfl hf)).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ f ≫
        (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv := by
  change ((Cochain.fromSingleMk f (zero_add n)).rightShift n 0 (zero_add n)).v
    0 0 (add_zero 0) = _
  rw [Cochain.rightShift_v _ n 0 (zero_add n) 0 0 (add_zero 0) n (zero_add n),
    Cochain.fromSingleMk_v]
  exact Category.assoc _ _ _

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

private lemma map_fromSingle {X : C} {K : CochainComplex C ℤ} {n : ℤ}
    (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))
        (F.mapHomologicalComplex (.up ℤ)) =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (F.map f) (zero_add n) (n + 1) rfl
          (by change F.map f ≫ F.map (K.d n (n + 1)) = 0
              rw [← F.map_comp, hf, F.map_zero])) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, ShiftedHom.map,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    fromSingleMk_f_zero, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  dsimp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    CochainComplex.shiftFunctorObjXIso]
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, F.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  congr 1
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToHom_map]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects] {X Y : C} (I : InjectiveResolution Y)
  {n : ℕ} (f : X ⟶ I.cocomplex.X n)
  (hf : f ≫ I.cocomplex.d n (n + 1) = 0)

/-- Applying the functor to an Ext cocycle and identifying the mapped resolution
gives the actual cocycle of the mapped coefficient. -/
private lemma map_extMk_cocycle :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
        (ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
            (zero_add _) ((n : ℤ) + 1) rfl
            (by
              rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by simp)]
              simp [reassoc_of% hf])))
          (F.mapHomologicalComplex (.up ℤ))) ≫
        ((DerivedPlus.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv)⟦(n : ℤ)⟧' =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk
          (F.map f ≫ ((mapInjectiveResolution F I).cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n : ℤ) + 1) rfl
          (by
            rw [(mapInjectiveResolution F I).cochainComplex_d
              (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by simp)]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            change F.map f ≫ F.map (I.cocomplex.d n (n + 1)) ≫ _ = 0
            rw [← F.map_comp_assoc, hf, F.map_zero, zero_comp])) := by
  rw [← Category.assoc, map_fromSingle]
  erw [← Cocycle.equivHomShift_symm_postcomp, ← Cocycle.fromSingleMk_postcomp]
  have hc : F.map (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫
      (DerivedPlus.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv.f n =
    F.map f ≫ ((mapInjectiveResolution F I).cochainComplexXIso n n rfl).inv := by
    apply (cancel_mono ((mapInjectiveResolution F I).cochainComplexXIso n n rfl).hom).1
    simp only [F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change F.map f ≫ F.map (I.cocomplex.extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
      (DerivedPlus.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv.f n ≫
      (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat rfl).hom = _
    rw [DerivedPlus.mapExtendIso_inv_f_comp_extendXIso]
    erw [← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  congr 1
  apply Subtype.ext
  apply (Cochain.fromSingleEquiv (zero_add (n : ℤ))).injective
  dsimp only [Cocycle.fromSingleMk, Cocycle.mk_coe]
  erw [Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk]
  exact hc

variable [HasExt.{wC} C] [HasExt.{wD} D]

private lemma extMk_hom_aug [HasDerivedCategory C] :
    (I.extMk f (n + 1) rfl hf).hom ≫ (DerivedCategory.Q.map I.ι')⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n : ℤ) + 1) rfl
          (by
            rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by simp)]
            simp [reassoc_of% hf]))) DerivedCategory.Q := by
  rw [InjectiveResolution.extMk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp, ShiftedHom.comp_mk₀,
    Category.assoc, ← Functor.map_comp]
  erw [Category.id_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- The actual exact-functor map on Ext sends the existing resolution constructor
to the constructor for the mapped injective resolution. -/
lemma extMk_mapExactFunctor :
    (I.extMk f (n + 1) rfl hf).mapExactFunctor F =
      (mapInjectiveResolution F I).extMk (F.map f) (n + 1) rfl
        (by change F.map f ≫ F.map (I.cocomplex.d n (n + 1)) = 0
            rw [← F.map_comp, hf, F.map_zero]) := by
  ext
  apply (cancel_mono
    ((DerivedCategory.Q.map (mapInjectiveResolution F I).ι')⟦(n : ℤ)⟧')).1
  rw [Ext.mapExactFunctor_hom, extMk_hom_aug]
  have haug := DerivedPlusSource.localizedMappedResolutionIso_augmentation F I
  have haug' : (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      DerivedCategory.Q.map (mapInjectiveResolution F I).ι' =
    F.mapDerivedCategory.map (DerivedCategory.Q.map I.ι') ≫
      (DerivedPlusSource.localizedMappedResolutionIso F I).hom := by
    rw [← haug, Iso.hom_inv_id_app_assoc]
  simp only [Category.assoc]
  rw [← Functor.map_comp, haug', Functor.map_comp]
  have hm := ShiftedHom.map_comp (I.extMk f (n + 1) rfl hf).hom
    (ShiftedHom.mk₀ 0 rfl (DerivedCategory.Q.map I.ι')) (zero_add (n : ℤ))
    F.mapDerivedCategory
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] at hm
  rw [← reassoc_of% hm, extMk_hom_aug]
  simp only [DerivedPlusSource.localizedMappedResolutionIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp]
  let z := Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n : ℤ) + 1) rfl
      (by
        rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by simp)]
        simp [reassoc_of% hf]))
  have hn := ShiftedHom.map_naturality z F.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hn
  rw [reassoc_of% hn,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  have hq := ShiftedHom.map_comp
    (ShiftedHom.mk₀ 0 rfl ((F.mapCochainComplexSingleFunctor 0).inv.app X))
    ((ShiftedHom.map z (F.mapHomologicalComplex (.up ℤ))).comp
      (ShiftedHom.mk₀ 0 rfl
        (DerivedPlus.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv)
      (zero_add (n : ℤ))) (add_zero (n : ℤ)) DerivedCategory.Q
  simp only [ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hq
  have hpost := ShiftedHom.map_comp
    (ShiftedHom.map z (F.mapHomologicalComplex (.up ℤ)))
    (ShiftedHom.mk₀ 0 rfl
      (DerivedPlus.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv)
    (zero_add (n : ℤ)) DerivedCategory.Q
  simp only [ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀] at hpost
  erw [hpost] at hq
  erw [← hq]
  exact congrArg (fun a => ShiftedHom.map a DerivedCategory.Q)
    (map_extMk_cocycle F I f hf)


end Langlands.Cohomology.ExtResolutionMap

namespace Langlands.Cohomology.ExtResolutionMap

universe v

variable {C D : Type*} [Category.{v} C] [Abelian C] [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects] {X Y : C} (I : InjectiveResolution Y) (n : ℕ)
  [HasExt.{wC} C] [HasExt.{wD} D]

/-- Apply the actual functor to every coefficient morphism in the Hom complex
of an injective resolution. -/
def resolutionHomMap :
    ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      ((preadditiveCoyoneda.obj (op (F.obj X))).mapHomologicalComplex (.up ℕ)).obj
        (mapInjectiveResolution F I).cocomplex where
  f _ := AddCommGrpCat.ofHom F.mapAddHom
  comm' i j _ := by
    ext a
    exact (F.map_comp a (I.cocomplex.d i j)).symm

/-- On resolution homology, the existing exact-functor Ext map is the actual
map obtained by applying the functor to coefficient morphisms. -/
lemma extAddEquivHomology_symm_map
    (a : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology n) :
    (ExtRightDerived.extAddEquivHomology (F.obj X) (mapInjectiveResolution F I) n).symm
        (HomologicalComplex.homologyMap (resolutionHomMap F (X := X) I) n a) =
      ((ExtRightDerived.extAddEquivHomology X I n).symm a).mapExactFunctor F := by
  let K := ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := ((preadditiveCoyoneda.obj (op (F.obj X))).mapHomologicalComplex (.up ℕ)).obj
    (mapInjectiveResolution F I).cocomplex
  let ψ := resolutionHomMap F (X := X) I
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a
  change (ExtRightDerived.extAddEquivHomology (F.obj X) (mapInjectiveResolution F I) n).symm
      ((K.homologyπ n ≫ HomologicalComplex.homologyMap ψ n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change (ExtRightDerived.extAddEquivHomology (F.obj X) (mapInjectiveResolution F I) n).symm
    (L.homologyπ n (HomologicalComplex.cyclesMap ψ n c)) = _
  rw [ExtRightDerived.extAddEquivHomology_symm_homologyπ,
    ExtRightDerived.extAddEquivHomology_symm_homologyπ, extMk_mapExactFunctor]
  congr 1
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) c

/-- The forward resolution comparison carries the exact-functor Ext map to
the actual map on the Hom-resolution cohomology. -/
lemma extAddEquivHomology_map (a : Ext.{wC} X Y n) :
    ExtRightDerived.extAddEquivHomology (F.obj X) (mapInjectiveResolution F I) n
        (a.mapExactFunctor F) =
      HomologicalComplex.homologyMap (resolutionHomMap F (X := X) I) n
        (ExtRightDerived.extAddEquivHomology X I n a) := by
  apply (ExtRightDerived.extAddEquivHomology (F.obj X) (mapInjectiveResolution F I) n).symm.injective
  rw [AddEquiv.symm_apply_apply, extAddEquivHomology_symm_map, AddEquiv.symm_apply_apply]

end Langlands.Cohomology.ExtResolutionMap
