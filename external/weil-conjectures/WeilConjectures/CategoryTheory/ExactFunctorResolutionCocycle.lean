/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact-functor transport of a resolution cocycle

Source: Stacks Project, Derived Categories, Tag 013P; Cohomology, Tag 01FB.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle)
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private noncomputable def comparisonExtension
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Additive]
    {A : C} {B : D} (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex) :
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex ⟶
      I.cochainComplex where
  f n := if hn : 0 ≤ n then
    L.map (R.cochainComplexXIso n n.toNat (Int.toNat_of_nonneg hn)).hom ≫
      e.f n.toNat ≫ (I.cochainComplexXIso n n.toNat (Int.toNat_of_nonneg hn)).inv
    else 0
  comm' n m h := by
    change n + 1 = m at h
    subst m
    by_cases hn : 0 ≤ n
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp]
      simp only [Int.natCast_nonneg, dite_true, Int.toNat_natCast,
        Functor.mapHomologicalComplex_obj_d]
      rw [R.cochainComplex_d _ _ k (k + 1) rfl (by simp),
        I.cochainComplex_d _ _ k (k + 1) rfl (by simp)]
      simp only [Functor.map_comp, Category.assoc,
        Iso.inv_hom_id_assoc]
      simp only [Iso.inv_hom_id_map_assoc]
      simpa only [Category.assoc, Functor.mapHomologicalComplex_obj_d] using
        congrArg (fun t ↦ L.map (R.cochainComplexXIso k k rfl).hom ≫ t ≫
          (I.cochainComplexXIso ((k + 1 : ℕ) : ℤ) (k + 1) rfl).inv)
        (e.comm k (k + 1))
    · exact (L.map_isZero (R.cochainComplex.isZero_of_isStrictlyGE 0 n (by lia))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonExtension_f
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Additive]
    {A : C} {B : D} (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (q : ℕ) :
    (comparisonExtension L R I e).f q =
      L.map (R.cochainComplexXIso q q rfl).hom ≫ e.f q ≫
        (I.cochainComplexXIso q q rfl).inv := by
  simp [comparisonExtension]

set_option backward.isDefEq.respectTransparency false in
/-- The derived-category morphism equality underlying exact-functor cocycle transport.

Source: Stacks Project, Derived Categories, Tag 013P; Cohomology, Tag 01FB.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle-hom)
The proof extends the supplied comparison to integer complexes, applies the
exact-functor formula for `Ext.mapExactFunctor_hom`, and simplifies the
single-complex and shift isomorphisms. -/
theorem exactFunctor_resolution_cocycle_hom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (f : L.obj A ⟶ B)
    (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (he : L.map (R.ι.f 0) ≫ e.f 0 = f ≫ I.ι.f 0)
    {P : C} (q : ℕ) (a : P ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (hc : (L.map a ≫ e.f q) ≫ I.cocomplex.d q (q + 1) = 0) :
    (((R.extMk a (q + 1) rfl ha).mapExactFunctor L).comp
      (Abelian.Ext.mk₀ f) (add_zero q)).hom =
      (I.extMk (L.map a ≫ e.f q) (q + 1) rfl hc).hom := by
  let φ := comparisonExtension L R I e
  have haug : (L.mapCochainComplexSingleFunctor 0).inv.app A ≫
      (L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ =
      (CochainComplex.singleFunctor D 0).map f ≫ I.ι' := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only [φ]
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, comparisonExtension_f]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      InjectiveResolution.ι'_f_zero, Functor.map_comp, Category.assoc]
    simp only [Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex, CochainComplex.singleFunctor,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Functor.comp_obj, Int.cast_ofNat_Int, Iso.inv_hom_id_map_assoc,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv]
    erw [Category.id_comp, Category.id_comp, reassoc_of% he]
    erw [L.map_id, Category.id_comp, Category.id_comp, Category.id_comp]
  have hsource : (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj P) =
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).inv.app P) := by
    simpa only [CochainComplex.singleFunctor] using!
      L.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app P
  have hden : L.mapDerivedCategoryFactors.inv.app R.cochainComplex ≫
      L.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app A ≫
      (DerivedCategory.singleFunctor D 0).map f =
      DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map I.ι') := by
    rw [← cancel_epi (DerivedCategory.Q.map
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι'))]
    erw [L.mapDerivedCategoryFactors.inv.naturality_assoc,
      ← L.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
      L.mapDerivedCategory.map_id, Category.id_comp]
    have hs := L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app A
    simp only [CochainComplex.singleFunctor] at hs
    erw [reassoc_of% hs]
    rw [← cancel_epi (DerivedCategory.Q.map
      ((L.mapCochainComplexSingleFunctor 0).inv.app A))]
    simp only [← Functor.map_comp_assoc]
    erw [haug]
    simp [Functor.map_comp, DerivedCategory.singleFunctor, CochainComplex.singleFunctor]
  let b := a ≫ (R.cochainComplexXIso q q rfl).inv
  have hb : b ≫ R.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    simp [b, R.cochainComplex_d (q : ℤ) ((q : ℤ) + 1) q (q + 1) rfl (by simp),
      reassoc_of% ha]
  have hbc : (L.map b ≫ φ.f (q : ℤ)) ≫
      I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    simp only [b, φ, comparisonExtension_f, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_map_assoc]
    rw [I.cochainComplex_d (q : ℤ) ((q : ℤ) + 1) q (q + 1) rfl (by simp)]
    simp only [Iso.inv_hom_id_assoc, reassoc_of% hc, zero_comp]
  have hnum : (L.mapCochainComplexSingleFunctor 0).inv.app P ≫
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.fromSingleMk b (zero_add (q : ℤ)) _ rfl hb))
          (L.mapHomologicalComplex (.up ℤ)) ≫ φ⟦(q : ℤ)⟧' =
      CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.fromSingleMk (L.map b ≫ φ.f (q : ℤ))
          (zero_add (q : ℤ)) _ rfl hbc) := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp [ShiftedHom.map]
    simp only [CochainComplex.singleFunctor, Functor.comp_obj,
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom,
      Category.id_comp, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_inv_app,
      ↓reduceDIte, eqToHom_refl, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
      CochainComplex.HomComplex.Cocycle.homOf_f,
      CochainComplex.HomComplex.Cocycle.rightShift_coe,
      CochainComplex.HomComplex.Cocycle.fromSingleMk_coe, zero_add,
      CochainComplex.HomComplex.Cochain.rightShift_v,
      CochainComplex.HomComplex.Cochain.fromSingleMk_v,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.inv,
      Functor.map_comp,
      Category.comp_id, Category.assoc, eqToHom_naturality]
    erw [eqToHom_map]
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mapExactFunctor_hom,
    InjectiveResolution.extMk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.comp_mk₀, Category.assoc]
  rw [← ShiftedHom.comp_map,
    ← ShiftedHom.map_naturality_2 _ L.mapDerivedCategoryFactors]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  erw [reassoc_of% hsource]
  erw [Category.comp_id, Category.comp_id]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hden,
    Functor.map_comp]
  rw [ShiftedHom.comp_map]
  have hnum' :
      (ShiftedHom.mk₀ 0 rfl ((L.mapCochainComplexSingleFunctor 0).inv.app P)).comp
        ((ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (CochainComplex.HomComplex.Cocycle.fromSingleMk b (zero_add (q : ℤ)) _ rfl hb))
            (L.mapHomologicalComplex (.up ℤ))).comp
              (ShiftedHom.mk₀ 0 rfl φ) (zero_add _)) (add_zero _) =
      CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.fromSingleMk (L.map b ≫ φ.f (q : ℤ))
          (zero_add (q : ℤ)) _ rfl hbc) := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc] using hnum
  have hn := congrArg (fun t ↦ ShiftedHom.map t DerivedCategory.Q) hnum'
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.map_mk₀] at hn
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hn
  have hbφ : L.map b ≫ φ.f (q : ℤ) =
      L.map a ≫ e.f q ≫ (I.cochainComplexXIso q q rfl).inv := by
    simp [b, φ, comparisonExtension_f, Functor.map_comp]
  simp only [hbφ] at hn
  erw [reassoc_of% hn]
  congr 3

/-- An augmented chain comparison computes exact-functor transport of Ext,
followed by the coefficient morphism lifted by that comparison.

Source: Stacks Project, Derived Categories, Tag 013P, lemma-morphisms-lift;
Cohomology, Tag 01FB, remark-explain-arrow.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle)

Proof: Extend the natural-number resolutions by zero to integer cochain complexes.
The augmentation of R is a quasi-isomorphism; exactness of L preserves it.
The commutation at degree zero of e with the augmentations gives a commuting square
from the single complex on L(A) into the extended complexes. In the derived category
invert the augmentations. The resulting equality identifies the map induced by e
with the coefficient morphism f. The closed map a represents R.extMk a under the
Hom-complex computation of Ext. Applying L to that representative and then e gives
L(a) followed by e in degree q. Thus exact-functor transport followed by Ext.mk₀ f
is precisely its class in I. Extension by zero also gives this argument in degree
zero; no negative boundary is introduced, and zero objects cause no exception. -/
theorem exactFunctor_resolution_cocycle
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (f : L.obj A ⟶ B)
    (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (he : L.map (R.ι.f 0) ≫ e.f 0 = f ≫ I.ι.f 0)
    {P : C} (q : ℕ) (a : P ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (hc : (L.map a ≫ e.f q) ≫ I.cocomplex.d q (q + 1) = 0) :
    ((R.extMk a (q + 1) rfl ha).mapExactFunctor L).comp
      (Abelian.Ext.mk₀ f) (add_zero q) = I.extMk (L.map a ≫ e.f q) (q + 1) rfl hc := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  apply Abelian.Ext.ext
  exact exactFunctor_resolution_cocycle_hom L f R I e he q a ha hc
