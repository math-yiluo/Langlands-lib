/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointLift
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The underlying object of a derived free algebra as a coproduct

Let `F` be an exact autoequivalence of a Grothendieck abelian category `C`, let
`I : D(C) ⥤ D(IsoAlgebra F)` be the functor induced by the free algebra functor
`S ↦ ∐ₙ Fⁿ S` and `U` the functor induced by the forgetful functor. For `X : D(C)`, the
object `U (I X)` is the coproduct of the objects `Fⁿ X`
(`CategoryTheory.Endofunctor.IsoAlgebra.isColimitDerivedFreeCofan`). The summand inclusions
`jₙ : Fⁿ X ⟶ U (I X)` satisfy `j₀ = η` up to the identification `F⁰ X ≅ X`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_iso_derivedFreeSummand_zero`), and
`jₙ₊₁` is `F jₙ` followed by the derived structure isomorphism of `I X`
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedFreeSummand_succ`).
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]

namespace Free

omit [Abelian C] [IsGrothendieckAbelian.{w} C] [F.Additive] in
@[simp]
lemma objMap_id (S : C) (n : ℤ) : objMap F (𝟙 S) n = 𝟙 _ := by
  have hp (k : ℕ) : posMap F (𝟙 S) k = 𝟙 _ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [posMap, ih]
      exact F.map_id _
  have hn (k : ℕ) : negMap F (𝟙 S) k = 𝟙 _ := by
    induction k with
    | zero => exact F.inv.map_id _
    | succ k ih =>
      simp only [negMap, ih]
      exact F.inv.map_id _
  rcases n with k | k
  · exact hp k
  · exact hn k

omit [Abelian C] [IsGrothendieckAbelian.{w} C] [F.Additive] in
@[simp]
lemma objMap_comp {S T T' : C} (f : S ⟶ T) (g : T ⟶ T') (n : ℤ) :
    objMap F (f ≫ g) n = objMap F f n ≫ objMap F g n := by
  have hp (k : ℕ) : posMap F (f ≫ g) k = posMap F f k ≫ posMap F g k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [posMap, ih]
      exact F.map_comp _ _
  have hn (k : ℕ) : negMap F (f ≫ g) k = negMap F f k ≫ negMap F g k := by
    induction k with
    | zero => exact F.inv.map_comp _ _
    | succ k ih =>
      simp only [negMap, ih]
      exact F.inv.map_comp _ _
  rcases n with k | k
  · exact hp k
  · exact hn k

/-- The functor `S ↦ Fⁿ S` of the `n`-th summand of the free algebra. -/
@[simps]
def objFunctor (n : ℤ) : C ⥤ C where
  obj S := obj F S n
  map f := objMap F f n

/-- The isomorphisms `F (Fⁿ S) ≅ Fⁿ⁺¹ S` as a natural isomorphism. -/
@[simps!]
def objSuccIso (n : ℤ) : objFunctor F n ⋙ F ≅ objFunctor F (n + 1) :=
  NatIso.ofComponents (fun S ↦ objSucc F S n) fun f ↦ map_objMap_comp_objSucc f n

omit [IsGrothendieckAbelian.{w} C] in
lemma objFunctor_isEquivalence_and_additive (n : ℤ) :
    (objFunctor F n).IsEquivalence ∧ (objFunctor F n).Additive := by
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  have : F.inv.Additive := inferInstanceAs F.asEquivalence.inverse.Additive
  rcases n with k | k
  · induction k with
    | zero =>
      let e : 𝟭 C ≅ objFunctor F (Int.ofNat 0) :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
          (Category.comp_id _).trans (Category.id_comp _).symm
      exact ⟨Functor.isEquivalence_of_iso e, Functor.additive_of_iso e⟩
    | succ k ih =>
      obtain ⟨_, _⟩ := ih
      let e : objFunctor F (Int.ofNat k) ⋙ F ≅ objFunctor F (Int.ofNat (k + 1)) :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
          (Category.comp_id _).trans (Category.id_comp _).symm
      exact ⟨Functor.isEquivalence_of_iso e, Functor.additive_of_iso e⟩
  · induction k with
    | zero =>
      let e : F.inv ≅ objFunctor F (Int.negSucc 0) :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
          (Category.comp_id _).trans (Category.id_comp _).symm
      exact ⟨Functor.isEquivalence_of_iso e, Functor.additive_of_iso e⟩
    | succ k ih =>
      obtain ⟨_, _⟩ := ih
      let e : objFunctor F (Int.negSucc k) ⋙ F.inv ≅ objFunctor F (Int.negSucc (k + 1)) :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
          (Category.comp_id _).trans (Category.id_comp _).symm
      exact ⟨Functor.isEquivalence_of_iso e, Functor.additive_of_iso e⟩

instance (n : ℤ) : (objFunctor F n).IsEquivalence :=
  (objFunctor_isEquivalence_and_additive F n).1

instance (n : ℤ) : (objFunctor F n).Additive :=
  (objFunctor_isEquivalence_and_additive F n).2

/-- The inclusion of the `n`-th summand `Fⁿ S` into the free algebra `∐ₙ Fⁿ S`. -/
@[simps]
def summandι (n : ℤ) : objFunctor F n ⟶ functor F ⋙ forget F where
  app S := Sigma.ι (obj F S) n
  naturality _ _ f := (Sigma.ι_map (objMap F f) n).symm

end Free

/-- The underlying complex of the free algebra on a complex `K` is the coproduct of the
complexes `Fⁿ K`, the coproduct being computed degreewise. -/
def isColimitFreeCofanComplex (K : CochainComplex C ℤ) :
    IsColimit (Cofan.mk
      (((Free.functor F ⋙ forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      fun n ↦ (NatTrans.mapHomologicalComplex (Free.summandι F n) (ComplexShape.up ℤ)).app K) :=
  HomologicalComplex.isColimitOfEval _ _ fun i ↦
    (isColimitMapCoconeCofanMkEquiv _ _ _).symm (coproductIsCoproduct (Free.obj F (K.X i)))

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- The derived summand inclusions `jₙ : Fⁿ X ⟶ U (I X)`. -/
def derivedFreeSummand (n : ℤ) :
    (Free.objFunctor F n).mapDerivedCategory ⟶
      (Free.functor F).mapDerivedCategory ⋙ (forget F).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatTrans (Free.summandι F n) ≫
    (Functor.mapDerivedCategoryCompIso (Free.functor F) (forget F)).inv

/-- The identification of `U (I (Q K))` with the localization of the underlying complex of the
free algebra on `K`. -/
def derivedFreeForgetIso (K : CochainComplex C ℤ) :
    (forget F).mapDerivedCategory.obj ((Free.functor F).mapDerivedCategory.obj
      (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        (((Free.functor F ⋙ forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (forget F).mapDerivedCategory.mapIso ((Free.functor F).mapDerivedCategoryFactors.app K) ≪≫
    (forget F).mapDerivedCategoryFactors.app
      (((Free.functor F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

@[reassoc]
lemma derivedFreeSummand_app_Q_obj (n : ℤ) (K : CochainComplex C ℤ) :
    (derivedFreeSummand F n).app (DerivedCategory.Q.obj K) ≫ (derivedFreeForgetIso F K).hom =
      (Free.objFunctor F n).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (Free.summandι F n) (ComplexShape.up ℤ)).app K) := by
  simp only [derivedFreeSummand, derivedFreeForgetIso, NatTrans.comp_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj_comp_factors (Free.functor F) (forget F) K,
    Functor.mapDerivedCategoryNatTrans_fac]

/-- **The derived free algebra is a coproduct.** The underlying object `U (I X)` of the free
algebra on `X : D(C)` is the coproduct of the objects `Fⁿ X`, with inclusions the derived
summand inclusions. -/
def isColimitDerivedFreeCofan (X : DerivedCategory C) :
    IsColimit (Cofan.mk
      ((forget F).mapDerivedCategory.obj ((Free.functor F).mapDerivedCategory.obj X))
      fun n ↦ (derivedFreeSummand F n).app X) := by
  have : Abelian.HasKInjectiveResolutions C :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  have hK : IsColimit (Cofan.mk
      ((forget F).mapDerivedCategory.obj ((Free.functor F).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)))
      fun n ↦ (derivedFreeSummand F n).app (DerivedCategory.Q.obj K)) :=
    isColimitCofanMkOfIso (DerivedCategory.isColimitCofanMkQObj (isColimitFreeCofanComplex F K))
      (fun n ↦ (Free.objFunctor F n).mapDerivedCategoryFactors.app K)
      (derivedFreeForgetIso F K) (derivedFreeSummand_app_Q_obj F · K)
  exact isColimitCofanMkOfIso hK (fun n ↦ (Free.objFunctor F n).mapDerivedCategory.mapIso e.symm)
    (((Free.functor F).mapDerivedCategory ⋙ (forget F).mapDerivedCategory).mapIso e.symm)
    (fun n ↦ ((derivedFreeSummand F n).naturality e.inv).symm)

/-- On the image of a complex `K`, the unit `X ⟶ U (I X)` of the derived free adjunction is the
localization of the unit of the free adjunction. -/
lemma freeWeilDerivedAdjunction_unit_app_Q_obj (K : CochainComplex C ℤ) :
    (freeWeilDerivedAdjunction F).unit.app (DerivedCategory.Q.obj K) ≫
        (derivedFreeForgetIso F K).hom =
      DerivedCategory.Q.map
        (((Free.adjunction F).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) := by
  let : CatCommSq ((Free.functor F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (Free.functor F).mapDerivedCategory :=
    ⟨(Free.functor F).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((forget F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (forget F).mapDerivedCategory :=
    ⟨(forget F).mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.localization_unit_app
    ((Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (Free.functor F).mapDerivedCategory (forget F).mapDerivedCategory K
  have hU : (CatCommSq.iso ((forget F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (forget F).mapDerivedCategory).hom.app
        (((Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) =
      (forget F).mapDerivedCategoryFactors.inv.app
        (((Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) := rfl
  have hI : (CatCommSq.iso ((Free.functor F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Free.functor F).mapDerivedCategory).hom.app K =
      (Free.functor F).mapDerivedCategoryFactors.inv.app K := rfl
  rw [hU, hI] at h
  simp only [freeWeilDerivedAdjunction, Adjunction.mapExactDerivedCategory]
  erw [h]
  simp only [derivedFreeForgetIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The summand inclusion `j₀ : F⁰ X ⟶ U (I X)` is the unit of the derived free adjunction, up to
an isomorphism `F⁰ X ≅ X`. -/
theorem exists_iso_derivedFreeSummand_zero (X : DerivedCategory C) :
    ∃ ζ : (Free.objFunctor F 0).mapDerivedCategory.obj X ≅ X,
      (derivedFreeSummand F 0).app X = ζ.hom ≫ (freeWeilDerivedAdjunction F).unit.app X := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let c : ((Free.objFunctor F 0).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅ K :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by simp)
  let ζK := (Free.objFunctor F 0).mapDerivedCategoryFactors.app K ≪≫ DerivedCategory.Q.mapIso c
  have hK : (derivedFreeSummand F 0).app (DerivedCategory.Q.obj K) =
      ζK.hom ≫ (freeWeilDerivedAdjunction F).unit.app (DerivedCategory.Q.obj K) := by
    rw [← cancel_mono (derivedFreeForgetIso F K).hom, derivedFreeSummand_app_Q_obj,
      Category.assoc, freeWeilDerivedAdjunction_unit_app_Q_obj]
    simp only [ζK, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
      ← DerivedCategory.Q.map_comp]
    congr 2
    ext i
    simp only [NatTrans.mapHomologicalComplex_app_f, Free.summandι_app, Functor.comp_obj,
      Free.adjunction, forget_obj, HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom,
      Adjunction.mapHomologicalComplex_unit_app_f, Adjunction.mkOfHomEquiv_unit_app,
      Equiv.coe_fn_mk, id_hom_f, Category.id_comp, c]
    exact (Category.comp_id _).symm
  refine ⟨(Free.objFunctor F 0).mapDerivedCategory.mapIso e.symm ≪≫ ζK ≪≫ e, ?_⟩
  have h₁ := (derivedFreeSummand F 0).naturality e.hom
  have h₂ := (freeWeilDerivedAdjunction F).unit.naturality e.hom
  dsimp at h₁ h₂
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [h₂, ← reassoc_of% hK, ← h₁, ← Functor.map_comp_assoc, e.inv_hom_id, Functor.map_id,
    Category.id_comp]

/-- The derived structure isomorphism of a free algebra on a complex `K` is the localization of
the structure isomorphism of the free algebra. -/
@[reassoc]
lemma derivedStrIso_hom_app_derivedFree (K : CochainComplex C ℤ) :
    (derivedStrIso F).hom.app ((Free.functor F).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        (derivedFreeForgetIso F K).hom =
      F.mapDerivedCategory.map (derivedFreeForgetIso F K).hom ≫
        F.mapDerivedCategoryFactors.hom.app
          (((Free.functor F ⋙ forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (strNatIso F).hom
          (ComplexShape.up ℤ)).app (((Free.functor F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) := by
  simp only [derivedFreeForgetIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← (derivedStrIso F).hom.naturality_assoc]
  erw [derivedStrIso_hom_app_Q_obj F (((Free.functor F).mapHomologicalComplex _).obj K)]
  rfl

/-- The isomorphisms `Fⁿ⁺¹ X ≅ F (Fⁿ X)` on derived categories. -/
def derivedFreeSummandSuccIso (n : ℤ) :
    (Free.objFunctor F (n + 1)).mapDerivedCategory ≅
      (Free.objFunctor F n).mapDerivedCategory ⋙ F.mapDerivedCategory :=
  (Functor.mapDerivedCategoryNatIso (Free.objSuccIso F n)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The summand inclusion `jₙ₊₁ : Fⁿ⁺¹ X ⟶ U (I X)` is `F jₙ` followed by the derived structure
isomorphism of the free algebra `I X`. -/
theorem derivedFreeSummand_succ (n : ℤ) (X : DerivedCategory C) :
    (derivedFreeSummand F (n + 1)).app X =
      (derivedFreeSummandSuccIso F n).hom.app X ≫
        F.mapDerivedCategory.map ((derivedFreeSummand F n).app X) ≫
        (derivedStrIso F).hom.app ((Free.functor F).mapDerivedCategory.obj X) := by
  suffices H : derivedFreeSummand F (n + 1) = (derivedFreeSummandSuccIso F n).hom ≫
      Functor.whiskerRight (derivedFreeSummand F n) F.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Free.functor F).mapDerivedCategory (derivedStrIso F).hom by
    rw [H]
    simp
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp]
  rw [← cancel_mono (derivedFreeForgetIso F K).hom, derivedFreeSummand_app_Q_obj,
    Category.assoc, Category.assoc, derivedStrIso_hom_app_derivedFree, ← Functor.map_comp_assoc,
    derivedFreeSummand_app_Q_obj, Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [derivedFreeSummandSuccIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj_comp_factors_assoc,
    mapDerivedCategoryNatIso_inv_app_Q_obj_comp_factors_assoc, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp]
  congr 2
  ext i
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Free.summandι_app, Free.objSuccIso_inv_app,
    strNatIso_hom_app]
  rw [Iso.eq_inv_comp]
  exact (Free.map_ι_comp_str F (K.X i) n).symm

end CategoryTheory.Endofunctor.IsoAlgebra
