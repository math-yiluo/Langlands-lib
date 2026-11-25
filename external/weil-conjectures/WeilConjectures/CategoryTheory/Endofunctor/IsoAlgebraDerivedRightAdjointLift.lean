/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!
# Lifting equivariant morphisms to the derived category of algebras

Let `F` be an exact autoequivalence of a Grothendieck abelian category `C`, and let
`U : D(IsoAlgebra F) ⥤ D(C)` be the functor induced by forgetting the structure isomorphisms.
Every object `U A` carries the derived structure isomorphism `F (U A) ≅ U A`
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso`), natural in `A`. This file shows that a
morphism `g : U A ⟶ U B` which commutes with these structure isomorphisms is of the form `U f`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_mapDerivedCategory_map_eq`).

The proof uses the free resolution triangle `I U A ⟶ I U A ⟶ A ⟶ (I U A)[1]`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`), whose first morphism
is `1 - τ` for the derived shift `τ` of the free algebra
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedFreeShift`) followed by the structure
isomorphism. The morphism `I g ≫ ε : I U A ⟶ B` is killed by `1 - τ` by equivariance of `g`,
hence factors through the counit `I U A ⟶ A`.

Since `U` reflects isomorphisms, an equivariant isomorphism `U A ≅ U B` lifts to an isomorphism
`A ≅ B` (`CategoryTheory.Endofunctor.IsoAlgebra.nonempty_iso_of_forget_mapDerivedCategory_iso`).
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]

namespace Free

omit [F.Additive] in
@[simp]
lemma functor_map {X Y : C} (f : X ⟶ Y) : (functor F).map f = map f :=
  rfl

/-- The morphism of free algebras `∐ₙ Fⁿ X ⟶ ∐ₙ Fⁿ (F X)` mapping the summand `F⁰ X = X` to
the summand `F⁻¹ (F X)` by the unit of the equivalence `F`. -/
def shiftHom (X : C) : (functor F).obj X ⟶ (functor F).obj (F.obj X) :=
  desc ((functor F).obj (F.obj X))
    ((F.asEquivalence.unitIso.app X).hom ≫ Sigma.ι (obj F (F.obj X)) (Int.negSucc 0))

omit [F.Additive] in
@[reassoc]
lemma ι_shiftHom_hom_f (X : C) :
    Sigma.ι (obj F X) 0 ≫ (shiftHom F X).hom.f =
      (F.asEquivalence.unitIso.app X).hom ≫ Sigma.ι (obj F (F.obj X)) (Int.negSucc 0) :=
  ι_desc_hom_f _ _

/-- The morphisms `Free.shiftHom F X` as a natural transformation. -/
@[simps]
def shiftNatTrans : functor F ⟶ F ⋙ functor F where
  app := shiftHom F
  naturality X Y f := by
    apply hom_ext
    simp only [Functor.comp_map, comp_hom_f,
      functor_map, map_hom_f, Sigma.ι_map_assoc, objMap_zero, ι_shiftHom_hom_f,
      ι_shiftHom_hom_f_assoc]
    rw [Sigma.ι_map, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Sigma.ι (obj F (F.obj Y)) (Int.negSucc 0))
      (F.asEquivalence.unitIso.hom.naturality f)

omit [Abelian C] [IsGrothendieckAbelian.{w} C] [F.Additive] in
/-- The section `F⁻¹(φ) ∘ η : M ⟶ F⁻¹ M` of the morphism `F⁻¹ M ⟶ M` induced by the identity of
an algebra `(M, φ)` on the summand `F⁻¹ M` of the free algebra. -/
lemma unit_comp_map_str_comp_hom (M : IsoAlgebra F) :
    ((F.asEquivalence.unitIso.app M.carrier).hom ≫ F.inv.map M.str.hom) ≫
      hom M (𝟙 M.carrier) (Int.negSucc 0) = 𝟙 M.carrier := by
  apply F.map_injective
  have e : F.map (hom M (𝟙 M.carrier) (Int.negSucc 0)) =
      (F.asEquivalence.counitIso.app M.carrier).hom ≫ M.str.inv := by
    simp only [hom, negHom, objSucc, Functor.map_preimage]
    exact congrArg (_ ≫ ·) (Category.id_comp M.str.inv)
  have h : F.map (F.inv.map M.str.hom) ≫ (F.asEquivalence.counitIso.app M.carrier).hom =
      (F.asEquivalence.counitIso.app (F.obj M.carrier)).hom ≫ M.str.hom :=
    F.asEquivalence.counitIso.hom.naturality M.str.hom
  rw [F.map_comp, F.map_comp, Category.assoc, e, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  erw [F.asEquivalence.functor_unit_comp]
  exact (F.map_id _).symm

end Free

/-- The endomorphism `τ` of the free algebra on the underlying object of an algebra `(M, φ)`
which maps the summand `M` to the summand `F⁻¹ M` by `F⁻¹(φ) ∘ η`, i.e. the composite of the
shift `Free.shiftHom` with the free functor applied to `φ`. -/
def freeShift : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F :=
  Functor.whiskerLeft (forget F) (Free.shiftNatTrans F) ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (strNatIso F).hom (Free.functor F)

omit [F.Additive] in
lemma ι_freeShift_app_hom_f (M : IsoAlgebra F) :
    Sigma.ι (Free.obj F M.carrier) 0 ≫ ((freeShift F).app M).hom.f =
      ((F.asEquivalence.unitIso.app M.carrier).hom ≫ F.inv.map M.str.hom) ≫
        Sigma.ι (Free.obj F M.carrier) (Int.negSucc 0) := by
  simp only [freeShift, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, comp_hom_f, Category.id_comp, Free.functor_map,
    Free.map_hom_f, Free.shiftNatTrans_app,
    strNatIso_hom_app, Category.assoc]
  erw [Free.ι_shiftHom_hom_f_assoc, Sigma.ι_map]
  rfl

section Factors

variable {A B E : Type*} [Category A] [Category B] [Category E] [Abelian A] [Abelian B]
  [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
  (P : A ⥤ B) (P' : B ⥤ E) [P.Additive] [P'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P']

/-- `Functor.mapDerivedCategoryCompIso_fac` with the identity comparison of
`Functor.mapHomologicalComplexCompIso` cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_Q_obj_comp_factors (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso P P').inv.app (DerivedCategory.Q.obj K) ≫
      P'.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
      P'.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (P ⋙ P').mapDerivedCategoryFactors.hom.app K := by
  rw [← Functor.mapDerivedCategoryCompIso_fac]
  have h : (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ P')) (ComplexShape.up ℤ)).hom.app
      K = 𝟙 _ := by
    ext n
    simp
  rw [h]
  simp

/-- The inverse of `Functor.mapDerivedCategoryNatIso e` on the image of a complex is the levelwise
inverse of `e`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_inv_app_Q_obj_comp_factors {P₁ P₂ : A ⥤ B} [P₁.Additive]
    [P₂.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
    [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂] (e : P₁ ≅ P₂)
    (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Q.obj K) ≫
        P₁.mapDerivedCategoryFactors.hom.app K =
      P₂.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K) := by
  rw [← cancel_epi ((Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, Functor.mapDerivedCategoryNatIso_fac_assoc,
    ← DerivedCategory.Q.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
    e.hom_inv_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app, DerivedCategory.Q.map_id,
    Category.comp_id]

end Factors

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- The derived structure isomorphism `F (U A) ≅ U A` of an object `A` of the derived category of
algebras, where `U` is induced by the forgetful functor. -/
def derivedStrIso :
    (forget F).mapDerivedCategory ⋙ F.mapDerivedCategory ≅ (forget F).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (forget F) F ≪≫
    Functor.mapDerivedCategoryNatIso (strNatIso F)

omit [IsGrothendieckAbelian.{w} C] in
/-- The derived structure isomorphism on the image of a complex is the levelwise structure
isomorphism. -/
@[reassoc]
lemma derivedStrIso_hom_app_Q_obj (K : CochainComplex (IsoAlgebra F) ℤ) :
    (derivedStrIso F).hom.app (DerivedCategory.Q.obj K) ≫
        (forget F).mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (strNatIso F).hom (ComplexShape.up ℤ)).app K) := by
  simp only [derivedStrIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← mapDerivedCategoryCompIso_hom_app_Q_obj_comp_factors (forget F) F K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The derived shift `I ⟶ I ∘ F` of free algebras, induced by `Free.shiftNatTrans`. -/
def derivedFreeShift :
    (Free.functor F).mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatTrans (Free.shiftNatTrans F) ≫
    (Functor.mapDerivedCategoryCompIso F (Free.functor F)).inv

@[reassoc]
lemma derivedFreeShift_app_Q_obj (X : CochainComplex C ℤ) :
    (derivedFreeShift F).app (DerivedCategory.Q.obj X) ≫
        (Free.functor F).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        (Free.functor F).mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) =
      (Free.functor F).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (Free.shiftNatTrans F) (ComplexShape.up ℤ)).app X) := by
  simp only [derivedFreeShift, NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj_comp_factors F (Free.functor F) X,
    Functor.mapDerivedCategoryNatTrans_fac]

/-- The derived endomorphism `τ` of `I U`: the derived shift followed by the free functor applied
to the derived structure isomorphism. -/
def derivedFreeShiftStr :
    (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory ⟶
      (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory :=
  Functor.whiskerLeft _ (derivedFreeShift F) ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedStrIso F).hom _

lemma derivedFreeShiftStr_app_Q_obj (K : CochainComplex (IsoAlgebra F) ℤ) :
    (derivedFreeShiftStr F).app (DerivedCategory.Q.obj K) ≫
        (freeWeilLocalizationComponent F K).hom =
      (freeWeilLocalizationComponent F K).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (freeShift F) (ComplexShape.up ℤ)).app K) := by
  simp only [derivedFreeShiftStr, freeWeilLocalizationComponent, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, derivedStrIso_hom_app_Q_obj, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Functor.mapDerivedCategoryFactors_hom_naturality]
  rw [← Functor.comp_map F.mapDerivedCategory (Free.functor F).mapDerivedCategory,
    ← (derivedFreeShift F).naturality_assoc]
  erw [derivedFreeShift_app_Q_obj_assoc]
  rw [← DerivedCategory.Q.map_comp]
  congr 3
  ext n
  simp only [freeShift, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  erw [Category.id_comp]
  rfl

/-- **Lifting equivariant morphisms to the derived category of algebras.** A morphism
`g : U A ⟶ U B` between the underlying objects of objects of `D(IsoAlgebra F)` which commutes
with the derived structure isomorphisms `F (U A) ≅ U A` and `F (U B) ≅ U B` is the image of a
morphism `A ⟶ B`. -/
theorem exists_forget_mapDerivedCategory_map_eq {A B : DerivedCategory (IsoAlgebra F)}
    (g : (forget F).mapDerivedCategory.obj A ⟶ (forget F).mapDerivedCategory.obj B)
    (hg : (derivedStrIso F).hom.app A ≫ g =
      F.mapDerivedCategory.map g ≫ (derivedStrIso F).hom.app B) :
    ∃ f : A ⟶ B, (forget F).mapDerivedCategory.map f = g := by
  obtain ⟨θ, d, hθ, hd, -, -, -, dD, δ, hdD, -, -, hdist⟩ := exists_freeDerivedWeilResolution F
  have hθ' (M : IsoAlgebra F) : (θ M (Int.negSucc 0)).inv =
      (F.asEquivalence.unitIso.app M.carrier).hom ≫ F.inv.map M.str.hom := by
    refine ((Iso.comp_hom_eq_id _).1 ?_).symm
    rw [hθ]
    exact Free.unit_comp_map_str_comp_hom F M
  have hdτ (M : IsoAlgebra F) : d.app M = 𝟙 _ - (freeShift F).app M := by
    have key : Sigma.ι (Free.obj F M.carrier) 0 ≫ (forget F).map (d.app M) =
        Sigma.ι (Free.obj F M.carrier) 0 ≫ (forget F).map (𝟙 _ - (freeShift F).app M) := by
      rw [Functor.map_sub, Preadditive.comp_sub, hd M 0]
      erw [Functor.map_id, Category.comp_id]
      congr 1
      rw [Iso.trans_hom, Iso.symm_hom, hθ M 0, Free.hom_zero]
      erw [Category.id_comp]
      exact (congrArg (· ≫ Sigma.ι (Free.obj F M.carrier) (Int.negSucc 0)) (hθ' M)).trans
        (ι_freeShift_app_hom_f F M).symm
    exact Free.hom_ext key
  have hdD' : dD = 𝟙 _ - derivedFreeShiftStr F := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) (fun K ↦ ?_)
    have hK : (NatTrans.mapHomologicalComplex d (ComplexShape.up ℤ)).app K =
        𝟙 _ - (NatTrans.mapHomologicalComplex (freeShift F) (ComplexShape.up ℤ)).app K := by
      ext n
      simp [hdτ]
    rw [← cancel_mono (freeWeilLocalizationComponent F K).hom, hdD, NatTrans.app_sub,
      NatTrans.id_app, Preadditive.sub_comp, derivedFreeShiftStr_app_Q_obj, hK, Functor.map_sub,
      Functor.map_id, Preadditive.comp_sub, Category.comp_id, Category.id_comp]
  let adj := freeWeilDerivedAdjunction F
  let U := (forget F).mapDerivedCategory
  let I := (Free.functor F).mapDerivedCategory
  have hτ : (derivedFreeShiftStr F).app A ≫ I.map g = I.map g ≫ (derivedFreeShiftStr F).app B := by
    simp only [derivedFreeShiftStr, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp, Category.assoc]
    rw [← I.map_comp, hg, I.map_comp, ← Functor.comp_map F.mapDerivedCategory I,
      ← (derivedFreeShift F).naturality_assoc]
  have hx : dD.app A ≫ I.map g ≫ adj.counit.app B = 0 := by
    have hB : dD.app B ≫ adj.counit.app B = 0 := comp_distTriang_mor_zero₁₂ _ (hdist B)
    rw [hdD'] at hB ⊢
    simp only [NatTrans.app_sub, NatTrans.id_app, Preadditive.sub_comp, Category.id_comp] at hB ⊢
    rw [reassoc_of% hτ, ← sub_eq_zero.1 hB, sub_self]
  obtain ⟨f, hf⟩ := Triangle.yoneda_exact₂ _ (hdist A) _ hx
  refine ⟨f, ?_⟩
  have h₁ : (adj.homEquiv _ _).symm g = I.map g ≫ adj.counit.app B := adj.homEquiv_counit _ _ g
  have h₂ : adj.homEquiv _ _ (adj.counit.app A ≫ f) = U.map f := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, adj.right_triangle_components_assoc]
  have hf' : I.map g ≫ adj.counit.app B = adj.counit.app A ≫ f := hf
  rw [← h₂, ← hf', ← h₁]
  exact Equiv.apply_symm_apply _ g

/-- **Lifting equivariant isomorphisms to the derived category of algebras.** If the underlying
objects `U A` and `U B` of objects of `D(IsoAlgebra F)` are isomorphic through an isomorphism
which commutes with the derived structure isomorphisms `F (U A) ≅ U A` and `F (U B) ≅ U B`,
then `A` and `B` are isomorphic. -/
theorem nonempty_iso_of_forget_mapDerivedCategory_iso {A B : DerivedCategory (IsoAlgebra F)}
    (g : (forget F).mapDerivedCategory.obj A ≅ (forget F).mapDerivedCategory.obj B)
    (hg : (derivedStrIso F).hom.app A ≫ g.hom =
      F.mapDerivedCategory.map g.hom ≫ (derivedStrIso F).hom.app B) :
    Nonempty (A ≅ B) := by
  obtain ⟨f, hf⟩ := exists_forget_mapDerivedCategory_map_eq F g.hom hg
  have : IsIso ((forget F).mapDerivedCategory.map f) := by
    rw [hf]
    infer_instance
  have := isIso_of_isIso_forget_mapDerivedCategory_map f
  exact ⟨asIso f⟩

end CategoryTheory.Endofunctor.IsoAlgebra
