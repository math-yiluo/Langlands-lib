import Langlands.Cohomology.EquivariantComposite.AcyclicHomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Functoriality of the canonical Hom-cohomology localization map -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.EquivariantComposite

universe w w' v u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] {X : C} {Y : D}

/-- Applying an additive functor and precomposing the source, term by term. -/
def homComplexMap (a : Y ⟶ F.obj X) (K : CochainComplex C ℤ) :
    ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((preadditiveCoyoneda.obj (op Y)).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K) where
  f i := AddCommGrpCat.ofHom
    { toFun := fun b => a ≫ F.map b
      map_zero' := by simp
      map_add' := by intros; rw [F.map_add, Preadditive.comp_add] }
  comm' i j _ := by
    ext b
    exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) (F.map_comp _ _).symm)

/-- The localized Hom-cohomology class is represented by its actual cycle. -/
lemma homologyDerivedMap_homologyπ [HasDerivedCategory.{w} C]
    (X : C) (K : CochainComplex C ℤ) (n : ℤ)
    (c : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    homologyDerivedMap X K n
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).homologyπ n c) =
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk
            ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).iCycles n c)
            (zero_add n) (n + 1) rfl
            (ConcreteCategory.congr_hom
              (HomologicalComplex.iCycles_d
                (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K)
                n (n + 1)) c))) DerivedCategory.Q := by
  unfold homologyDerivedMap
  dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [ExtRightDerived.coyonedaHomologyAddEquiv_homologyπ, classDerivedMap_mk]
  congr 3
  apply Subtype.ext
  exact ExtRightDerived.coyonedaHomComplex_cycles_coe X K n c

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

/-- The shifted chain map of a cycle commutes with applying any additive
functor. No exactness or preservation of injectives is needed here. -/
lemma map_fromSingleMk {K : CochainComplex C ℤ} {n : ℤ}
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

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical localization map commutes with an exact functor on arbitrary
complexes, with an arbitrary map into the transformed source. -/
lemma homologyDerivedMap_map (a : Y ⟶ F.obj X) (K : CochainComplex C ℤ)
    (n : ℤ)
    (x : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    homologyDerivedMap Y ((F.mapHomologicalComplex (.up ℤ)).obj K) n
        (HomologicalComplex.homologyMap (homComplexMap F a K) n x) =
      (DerivedCategory.singleFunctor D 0).map a ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        ShiftedHom.map (homologyDerivedMap X K n x) F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧' := by
  let A := ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K
  let B := ((preadditiveCoyoneda.obj (op Y)).mapHomologicalComplex (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  let ψ := homComplexMap F a K
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (A.homologyπ n)).1 inferInstance x
  change homologyDerivedMap Y _ n ((A.homologyπ n ≫
    HomologicalComplex.homologyMap ψ n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change homologyDerivedMap Y _ n
    (B.homologyπ n (HomologicalComplex.cyclesMap ψ n c)) = _
  erw [homologyDerivedMap_homologyπ, homologyDerivedMap_homologyπ]
  have hc : B.iCycles n (HomologicalComplex.cyclesMap ψ n c) =
      a ≫ F.map (A.iCycles n c) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) c
  have hf : A.iCycles n c ≫ K.d n (n + 1) = 0 :=
    ConcreteCategory.congr_hom (A.iCycles_d n (n + 1)) c
  have hz :
      Cocycle.fromSingleMk (B.iCycles n (HomologicalComplex.cyclesMap ψ n c))
          (zero_add n) (n + 1) rfl
          (ConcreteCategory.congr_hom (B.iCycles_d n (n + 1))
            (HomologicalComplex.cyclesMap ψ n c)) =
        (Cocycle.fromSingleMk (F.map (A.iCycles n c))
          (zero_add n) (n + 1) rfl
          (by change F.map (A.iCycles n c) ≫ F.map (K.d n (n + 1)) = 0
              rw [← F.map_comp, hf, F.map_zero])).precomp
            ((singleFunctor D 0).map a) := by
    apply Subtype.ext
    change Cochain.fromSingleMk _ (zero_add n) =
      (Cochain.ofHom ((singleFunctor D 0).map a)).comp
        (Cochain.fromSingleMk _ (zero_add n)) (zero_add n)
    rw [← Cochain.fromSingleMk_precomp]
    exact congrArg (fun b => Cochain.fromSingleMk b (zero_add n)) hc
  erw [hz, Cocycle.equivHomShift_symm_precomp]
  dsimp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
    NatTrans.id_app]
  simp only [Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← map_fromSingleMk F]
  let z := Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk (A.iCycles n c) (zero_add n) (n + 1) rfl
      (ConcreteCategory.congr_hom (A.iCycles_d n (n + 1)) c))
  have hn := ShiftedHom.map_naturality z F.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hn
  change ShiftedHom.map
      (((singleFunctor D 0).map a) ≫
        (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
        ShiftedHom.map z (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q =
    (DerivedCategory.singleFunctor D 0).map a ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (ShiftedHom.map z DerivedCategory.Q) F.mapDerivedCategory ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧'
  rw [hn,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rfl

end Langlands.Cohomology.EquivariantComposite
