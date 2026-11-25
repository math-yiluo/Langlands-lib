/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Exactness and products for the localized scalar cone

Source: Stacks, Tags 06YS and 0941, the bounded finite-free tensor argument.
(blueprint: lem-coef-linear-scalar-cone-exact-products).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe v u w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CochainComplex.LinearScalarCone

open HomComplex

variable {R : Type r} [Ring R] {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]

private noncomputable abbrev cocone (s : R) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  SignedCoconeShift.coconeFunctor (𝟭 (CochainComplex A ℤ))
    (𝟭 (CochainComplex A ℤ)) (s • 𝟙 (𝟭 (CochainComplex A ℤ)))

private theorem scalar_cochain_comm (s : R) {K L : CochainComplex A ℤ}
    {n : ℤ} (a : Cochain K L n) :
    (Cochain.ofHom (s • 𝟙 K)).comp a (zero_add n) =
      a.comp (Cochain.ofHom (s • 𝟙 L)) (add_zero n) := by
  ext p q hpq
  simp

private theorem cocone_δ_inl {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    δ 0 1 (mappingCocone.inl f) =
      -(Cochain.ofHom f).comp (mappingCocone.inr f).1 (zero_add 1) := by
  simp only [mappingCocone.inl, Cochain.δ_rightShift (mappingCone.inl f)
    (-1) 0 1 (by omega) 0 (by omega), mappingCone.δ_inl]
  ext p q hpq
  simp only [mappingCocone.inr, Cocycle.rightShift_coe, Cocycle.ofHom_coe,
    Cochain.ofHom_comp]
  simp [Cochain.rightShift_v (n := 0) _ (-1) 1 (by omega) p q hpq p (by omega)]

private noncomputable def transposeTo (s : R) {K L : CochainComplex A ℤ}
    (f : (cocone (A := A) s).obj K ⟶ L) : K ⟶ (cochain s).obj L :=
  mappingCone.lift (s • 𝟙 L) ((mappingCocone.inr (s • 𝟙 K)).postcomp f)
    ((mappingCocone.inl (s • 𝟙 K)).comp (Cochain.ofHom f) (add_zero 0)) (by
      rw [δ_comp_ofHom, cocone_δ_inl, Cochain.neg_comp,
        Cochain.comp_assoc_of_first_is_zero_cochain]
      rw [scalar_cochain_comm]
      exact neg_add_cancel _)

private noncomputable def transposeFrom (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ (cochain (A := A) s).obj L) : (cocone s).obj K ⟶ L :=
  mappingCocone.desc (s • 𝟙 K)
    ((Cochain.ofHom f).comp (mappingCone.snd (s • 𝟙 L)) (zero_add 0))
    ((mappingCone.fst (s • 𝟙 L)).precomp f) (by
      rw [δ_ofHom_comp, mappingCone.δ_snd, Cochain.comp_neg,
        ← Cochain.comp_assoc_of_first_is_zero_cochain]
      rw [scalar_cochain_comm]
      exact neg_add_cancel _)

private theorem transpose_left_inv (s : R) {K L : CochainComplex A ℤ}
    (f : (cocone (A := A) s).obj K ⟶ L) :
    transposeFrom s (transposeTo s f) = f := by
  apply HomologicalComplex.hom_ext
  intro j
  apply SignedCoconeShift.cocone_ext_from
  · simp [transposeFrom, transposeTo, Cocycle.precomp, Cocycle.postcomp]
  · simp [transposeFrom, transposeTo, Cocycle.precomp, Cocycle.postcomp]

private theorem transpose_right_inv (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ (cochain (A := A) s).obj L) :
    transposeTo s (transposeFrom s f) = f := by
  apply HomologicalComplex.hom_ext
  intro j
  apply mappingCone.ext_to _ j (j + 1) rfl
  · simp [transposeFrom, transposeTo, Cocycle.precomp, Cocycle.postcomp]
  · simp [transposeFrom, transposeTo, Cocycle.precomp, Cocycle.postcomp]

private noncomputable def cochainAdjunction (s : R) : cocone (A := A) s ⊣ cochain s :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := transposeTo s
          invFun := transposeFrom s
          left_inv := transpose_left_inv s
          right_inv := transpose_right_inv s }
      homEquiv_naturality_left_symm := by
        intro K' K L f g
        apply HomologicalComplex.hom_ext
        intro j
        apply SignedCoconeShift.cocone_ext_from
        · simp [transposeFrom, SignedCoconeShift.coconeFunctor,
            SignedCoconeShift.coconeMap_inl_assoc, Cocycle.precomp]
        · simp [transposeFrom, SignedCoconeShift.coconeFunctor,
            SignedCoconeShift.coconeMap_inr_assoc, Cocycle.precomp]
      homEquiv_naturality_right := by
        intro K L L' f g
        apply HomologicalComplex.hom_ext
        intro j
        apply mappingCone.ext_to _ j (j + 1) rfl
        · simp [transposeTo, cochain, Cocycle.postcomp,
            ConeCoimage.map_f_fst_v, Category.assoc]
        · simp [transposeTo, cochain, Cocycle.postcomp,
            ConeCoimage.map_f_snd_v, Category.assoc] }

private noncomputable def first {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :=
  (mappingCone.fst f).1.v q (q + 1) rfl

private noncomputable def second {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :=
  (mappingCone.snd f).v q q (add_zero q)

private theorem cone_ext {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ)
    {M : A} {a b : M ⟶ (mappingCone f).X q}
    (h₁ : a ≫ first f q = b ≫ first f q)
    (h₂ : a ≫ second f q = b ≫ second f q) : a = b :=
  mappingCone.ext_to f q (q + 1) rfl h₁ h₂

private noncomputable def pair {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (q : ℤ) {M : A} (a : M ⟶ K.X (q + 1)) (b : M ⟶ L.X q) :
    M ⟶ (mappingCone f).X q :=
  a ≫ (mappingCone.inl f).v (q + 1) q (by omega) + b ≫ (mappingCone.inr f).f q

@[reassoc (attr := simp)]
private theorem pair_first {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (q : ℤ) {M : A} (a : M ⟶ K.X (q + 1)) (b : M ⟶ L.X q) :
    pair f q a b ≫ first f q = a := by
  simp [pair, first, Preadditive.add_comp]

@[reassoc (attr := simp)]
private theorem pair_second {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (q : ℤ) {M : A} (a : M ⟶ K.X (q + 1)) (b : M ⟶ L.X q) :
    pair f q a b ≫ second f q = b := by
  simp [pair, second, Preadditive.add_comp]

@[reassoc]
private theorem differential_first {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone f).d q (q + 1) ≫ first f (q + 1) =
      -(first f q ≫ K.d (q + 1) ((q + 1) + 1)) :=
  mappingCone.d_fst_v f q (q + 1) ((q + 1) + 1) rfl rfl

@[reassoc]
private theorem differential_second {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone f).d q (q + 1) ≫ second f (q + 1) =
      first f q ≫ f.f (q + 1) + second f q ≫ L.d q (q + 1) :=
  mappingCone.d_snd_v f q (q + 1) rfl

@[reassoc (attr := simp)]
private theorem scalar_map_first (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    ((cochain s).map f).f q ≫ first (s • 𝟙 L) q = first (s • 𝟙 K) q ≫ f.f (q + 1) :=
  ConeCoimage.map_f_fst_v _ _ _ _ (by simp) q (q + 1) rfl

@[reassoc (attr := simp)]
private theorem scalar_map_second (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    ((cochain s).map f).f q ≫ second (s • 𝟙 L) q = second (s • 𝟙 K) q ≫ f.f q :=
  ConeCoimage.map_f_snd_v _ _ _ _ (by simp) q

@[reassoc (attr := simp)]
private theorem inr_first {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone.inr f).f q ≫ first f q = 0 := by simp [first]

@[reassoc (attr := simp)]
private theorem inr_second {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone.inr f).f q ≫ second f q = 𝟙 _ := by simp [second]

@[reassoc]
private theorem scalar_d_first (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    ((cochain s).obj K).d q (q + 1) ≫ first (s • 𝟙 K) (q + 1) =
      -(first (s • 𝟙 K) q ≫ K.d (q + 1) ((q + 1) + 1)) :=
  differential_first (s • 𝟙 K) q

@[reassoc]
private theorem scalar_d_second (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    ((cochain s).obj K).d q (q + 1) ≫ second (s • 𝟙 K) (q + 1) =
      s • first (s • 𝟙 K) q + second (s • 𝟙 K) q ≫ K.d q (q + 1) := by
  simpa using differential_second (s • 𝟙 K) q

attribute [local irreducible] first second

private noncomputable def interchangeComponent (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    ((cochain s).obj (mappingCone f)).X q ⟶ (mappingCone ((cochain s).map f)).X q :=
  pair ((cochain s).map f) q
    (pair (s • 𝟙 K) (q + 1)
      (-(first (s • 𝟙 (mappingCone f)) q ≫ first f (q + 1)))
      (second (s • 𝟙 (mappingCone f)) q ≫ first f q))
    (pair (s • 𝟙 L) q
      (first (s • 𝟙 (mappingCone f)) q ≫ second f (q + 1))
      (second (s • 𝟙 (mappingCone f)) q ≫ second f q))

private noncomputable def interchangeInvComponent (s : R)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone ((cochain s).map f)).X q ⟶ ((cochain s).obj (mappingCone f)).X q :=
  pair (s • 𝟙 (mappingCone f)) q
    (pair f (q + 1)
      (-(first ((cochain s).map f) q ≫ first (s • 𝟙 K) (q + 1)))
      (second ((cochain s).map f) q ≫ first (s • 𝟙 L) q))
    (pair f q
      (first ((cochain s).map f) q ≫ second (s • 𝟙 K) (q + 1))
      (second ((cochain s).map f) q ≫ second (s • 𝟙 L) q))

@[reassoc (attr := simp)]
private theorem interchange_first_first (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    interchangeComponent s f q ≫ first ((cochain s).map f) q ≫
        first (s • 𝟙 K) (q + 1) =
      -(first (s • 𝟙 (mappingCone f)) q ≫ first f (q + 1)) := by
  simp [interchangeComponent]

@[reassoc (attr := simp)]
private theorem interchange_first_second (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    interchangeComponent s f q ≫ first ((cochain s).map f) q ≫
        second (s • 𝟙 K) (q + 1) =
      second (s • 𝟙 (mappingCone f)) q ≫ first f q := by
  simp [interchangeComponent]

@[reassoc (attr := simp)]
private theorem interchange_second_first (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    interchangeComponent s f q ≫ second ((cochain s).map f) q ≫ first (s • 𝟙 L) q =
      first (s • 𝟙 (mappingCone f)) q ≫ second f (q + 1) := by
  simp [interchangeComponent]

@[reassoc (attr := simp)]
private theorem interchange_second_second (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    interchangeComponent s f q ≫ second ((cochain s).map f) q ≫ second (s • 𝟙 L) q =
      second (s • 𝟙 (mappingCone f)) q ≫ second f q := by
  simp [interchangeComponent]

private theorem interchange_comm (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) :
    interchangeComponent s f q ≫ (mappingCone ((cochain s).map f)).d q (q + 1) =
      ((cochain s).obj (mappingCone f)).d q (q + 1) ≫ interchangeComponent s f (q + 1) := by
  apply cone_ext ((cochain s).map f) (q + 1)
  · apply cone_ext (s • 𝟙 K) ((q + 1) + 1)
    · simp only [Category.assoc, differential_first_assoc ((cochain s).map f) q,
        scalar_d_first s K (q + 1),
         interchange_first_first,
         Preadditive.comp_neg, Preadditive.neg_comp,
        neg_neg]
      erw [interchange_first_first_assoc, scalar_d_first_assoc]
      simp only [Preadditive.neg_comp, Category.assoc, Preadditive.comp_neg,
        differential_first, neg_neg]
    · simp only [Category.assoc, differential_first_assoc ((cochain s).map f) q,
        scalar_d_second s K (q + 1),
         interchange_first_first,
         interchange_first_second,
         Preadditive.comp_neg, Preadditive.neg_comp,
        Preadditive.comp_add, Linear.comp_smul,
        neg_add_rev, smul_neg, neg_neg]
      erw [interchange_first_second_assoc, scalar_d_second_assoc]
      simp only [Preadditive.add_comp, Category.assoc, Linear.smul_comp,
        differential_first, Preadditive.comp_neg]
      abel
  · apply cone_ext (s • 𝟙 L) (q + 1)
    · simp only [Category.assoc, differential_second_assoc ((cochain s).map f) q,
        scalar_map_first s f (q + 1),
        scalar_d_first s L q,
         interchange_second_first,
         Preadditive.comp_neg,
        Preadditive.comp_add, Preadditive.add_comp]
      erw [interchange_first_first_assoc, interchange_second_first_assoc,
        scalar_d_first_assoc]
      simp only [Preadditive.neg_comp, Category.assoc, differential_second,
        Preadditive.comp_add]
      abel
    · simp only [Category.assoc, differential_second_assoc ((cochain s).map f) q,
        scalar_map_second s f (q + 1),
        scalar_d_second s L q,
         interchange_second_first,
         interchange_second_second,
         Preadditive.comp_add, Preadditive.add_comp,
        Linear.comp_smul]
      erw [interchange_first_second_assoc, interchange_second_second_assoc,
        scalar_d_second_assoc]
      simp only [Preadditive.add_comp, Category.assoc, Linear.smul_comp,
        differential_second, Preadditive.comp_add]
      abel

private noncomputable def interchangeComponentIso (s : R)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    ((cochain s).obj (mappingCone f)).X q ≅ (mappingCone ((cochain s).map f)).X q where
  hom := interchangeComponent s f q
  inv := interchangeInvComponent s f q
  hom_inv_id := by
    apply cone_ext _ q
    · apply cone_ext _ (q + 1)
      all_goals simp [interchangeComponent, interchangeInvComponent, Category.assoc]
    · apply cone_ext _ q
      all_goals simp [interchangeComponent, interchangeInvComponent, Category.assoc]
  inv_hom_id := by
    apply cone_ext _ q
    · apply cone_ext _ (q + 1)
      all_goals simp [interchangeComponent, interchangeInvComponent, Category.assoc]
    · apply cone_ext _ q
      all_goals simp [interchangeComponent, interchangeInvComponent, Category.assoc]

private noncomputable def interchangeIso (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) : (cochain s).obj (mappingCone f) ≅ mappingCone ((cochain s).map f) :=
  HomologicalComplex.Hom.isoOfComponents (interchangeComponentIso s f) (by
    intro q p hp
    obtain rfl : p = q + 1 := hp.symm
    exact interchange_comm s f q)

@[simp]
private theorem interchangeIso_hom_f (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) : (interchangeIso s f).hom.f q = interchangeComponent s f q := rfl

attribute [local irreducible] interchangeIso interchangeComponentIso interchangeComponent

private theorem interchange_inclusion (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) :
    (cochain s).map (mappingCone.inr f) ≫ (interchangeIso s f).hom =
      mappingCone.inr ((cochain s).map f) := by
  ext q : 1
  simp only [HomologicalComplex.comp_f, interchangeIso_hom_f]
  apply cone_ext ((cochain s).map f) q
  · apply cone_ext (s • 𝟙 K) (q + 1)
    · simp only [Category.assoc, interchange_first_first, Preadditive.comp_neg,
        inr_first_assoc, zero_comp]
      erw [scalar_map_first_assoc s (mappingCone.inr f) q]
      simp only [inr_first, comp_zero, neg_zero]
    · simp only [Category.assoc, interchange_first_second, inr_first_assoc, zero_comp]
      erw [scalar_map_second_assoc s (mappingCone.inr f) q]
      simp only [inr_first, comp_zero]
  · apply cone_ext (s • 𝟙 L) q
    · simp only [Category.assoc, interchange_second_first, inr_second_assoc]
      erw [scalar_map_first_assoc s (mappingCone.inr f) q]
      simp only [inr_second, Category.comp_id]
    · simp only [Category.assoc, interchange_second_second, inr_second_assoc]
      erw [scalar_map_second_assoc s (mappingCone.inr f) q]
      simp only [inr_second, Category.comp_id]

private theorem scalar_commShift (s : R) :
    NatTrans.CommShift (s • 𝟙 (𝟭 (CochainComplex A ℤ))) ℤ where
  shift_comm n := by
    ext K j
    simp [Functor.commShiftIso_id_hom_app, Linear.comp_smul]

@[instance_reducible]
private noncomputable def coconeCommShift (s : R) :
    (cocone (A := A) s).CommShift ℤ := by
  let := scalar_commShift (A := A) s
  exact SignedCoconeShift.coconeCommShift _ _ _

private theorem cofiberMap_eq_coneMap
    {K L K' L' : CochainComplex A ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      mappingCone.map f g a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    mappingCone.map, mappingCone.desc, mappingCone.descCochain,
    HomComplex.Cochain.comp_v, mappingCone.inl, mappingCone.fst, mappingCone.snd,
    mappingCone.inr]

private noncomputable def coconeIso (s : R) :
    cocone (A := A) s ≅ cochain s ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (cofiberMap_eq_coneMap (s • 𝟙 K) (s • 𝟙 L) f f (by simp)))

private noncomputable def unshiftCoconeIso (s : R) :
    cocone (A := A) s ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ) ≅ cochain s :=
  Functor.isoWhiskerRight (coconeIso s) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)) ≪≫
    Functor.rightUnitor _

@[instance_reducible]
private noncomputable def cochainCommShift (s : R) :
    (cochain (A := A) s).CommShift ℤ := by
  let := coconeCommShift (A := A) s
  exact Functor.CommShift.ofIso (unshiftCoconeIso s) ℤ

private noncomputable def cochainShiftOne (s : R) (K : CochainComplex A ℤ) :
    (cochain s).obj (K⟦(1 : ℤ)⟧) ⟶ ((cochain s).obj K)⟦(1 : ℤ)⟧ :=
  (Functor.commShiftIso (cochain s) (self := cochainCommShift s) (1 : ℤ)).hom.app K

private theorem cochainShiftOne_eq (s : R) (K : CochainComplex A ℤ) :
    cochainShiftOne s K =
      (Functor.commShiftIso (cochain s) (self := cochainCommShift s) (1 : ℤ)).hom.app K := rfl

attribute [local irreducible] cochainShiftOne

private theorem unshiftCoconeIso_hom_f (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    ((unshiftCoconeIso s).hom.app K).f q =
      (((cochain s).obj K).XIsoOfEq (by omega : q + 1 + -1 = q)).hom := by
  simp [unshiftCoconeIso, coconeIso, shiftFunctorCompIsoId,
    CochainComplex.shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f,
    HomologicalComplex.XIsoOfEq, eqToHom_trans]

private theorem unshiftCoconeIso_inv_f (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    ((unshiftCoconeIso s).inv.app K).f q =
      (((cochain s).obj K).XIsoOfEq (by omega : q = q + 1 + -1)).hom := by
  simp only [Functor.comp_obj, smulArrow_obj, ConeCoimage.cone_obj, Arrow.mk_left,
    Arrow.mk_right, Arrow.mk_hom, shiftFunctor_obj_X', unshiftCoconeIso, Int.reduceNeg,
    coconeIso, shiftFunctorCompIsoId, Functor.isoWhiskerLeft_trans, Iso.trans_assoc,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, NatIso.ofComponents_inv_app, Iso.refl_inv,
    Category.id_comp, HomologicalComplex.comp_f, shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f',
    shiftFunctor_map_f', HomologicalComplex.id_f, eqToHom_trans_assoc]
  erw [Category.comp_id]

private theorem coconeShift_eq (s : R) (K : CochainComplex A ℤ) (n : ℤ) :
    (Functor.commShiftIso (cocone s) (self := coconeCommShift s) n).hom.app K =
      (SignedCoconeShift.signedCoconeShiftIso (s • 𝟙 K) n).hom := by
  let τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 (CochainComplex A ℤ) := s • 𝟙 _
  let := scalar_commShift (A := A) s
  change (SignedCoconeShift.coconeFunctorShiftIso (𝟭 _) (𝟭 _) τ K n).hom = _
  have hs : (τ.app K)⟦n⟧' = τ.app (K⟦n⟧) := by
    dsimp only [τ, NatTrans.app_smul, NatTrans.id_app, Functor.id_obj]
    simp only [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  dsimp only [SignedCoconeShift.coconeFunctorShiftIso, Iso.trans_hom,
    Functor.mapIso_hom]
  generalize he : (HomologicalComplex.homotopyCofiber.mapArrowIso
    (τ.app (K⟦n⟧)) ((τ.app K)⟦n⟧')
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
    (Arrow.isoMk' _ _ (((𝟭 (CochainComplex A ℤ)).commShiftIso n).app K)
      (((𝟭 (CochainComplex A ℤ)).commShiftIso n).app K)
      (NatTrans.shift_app_comm τ n K))).hom = e
  have hid : HEq e (𝟙 (mappingCone (τ.app (K⟦n⟧)))) := by
    subst e
    change HEq (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ _) _
    erw [cofiberMap_eq_coneMap]
    rotate_left
    · exact (NatTrans.shift_app_comm τ n K).symm
    simp only [Functor.commShiftIso_id_hom_app, Iso.app_hom]
    apply heq_of_eq
    change mappingCone.map (s • 𝟙 (K⟦n⟧)) (s • 𝟙 (K⟦n⟧)) (𝟙 _) (𝟙 _) _ = _
    exact mappingCone.map_id _
  cases hs
  have heq := eq_of_heq hid
  rw [heq]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem shift_inv_first (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    (mappingCone.shiftIso (s • 𝟙 K) 1).inv.f q ≫ first (s • 𝟙 K) (q + 1) =
      -first ((s • 𝟙 K)⟦(1 : ℤ)⟧') q := by
  apply mappingCone.ext_from _ (q + 1) q rfl <;>
    simp [mappingCone.shiftIso, first, Cochain.shift_v']

private theorem shift_inv_second (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    (mappingCone.shiftIso (s • 𝟙 K) 1).inv.f q ≫ second (s • 𝟙 K) (q + 1) =
      second ((s • 𝟙 K)⟦(1 : ℤ)⟧') q := by
  apply mappingCone.ext_from _ (q + 1) q rfl <;>
    simp [mappingCone.shiftIso, second, Cochain.shift_v']

private theorem cochainShiftOne_standard (s : R) (K : CochainComplex A ℤ) :
    HEq (cochainShiftOne s K) (mappingCone.shiftIso (s • 𝟙 K) 1).inv := by
  rw [cochainShiftOne_eq]
  let := coconeCommShift (A := A) s
  change HEq (((Functor.CommShift.ofIso (unshiftCoconeIso s) ℤ).commShiftIso 1).hom.app K) _
  apply heq_of_eq
  ext q : 1
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app,
    HomologicalComplex.comp_f, unshiftCoconeIso_hom_f, unshiftCoconeIso_inv_f,
    Functor.commShiftIso_comp_hom_app, shiftFunctor_map_f',
    Pretriangulated.shiftFunctor_commShiftIso_hom_app,
    HomologicalComplex.units_smul_f_apply, shiftFunctorComm_hom_app_f]
  rw [coconeShift_eq]
  dsimp only [SignedCoconeShift.signedCoconeShiftIso, Preadditive.smul_iso_hom,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  simp only [HomologicalComplex.units_smul_f_apply, HomologicalComplex.comp_f,
    shiftFunctor_map_f']
  simp only [Iso.app_hom, shiftFunctorComm_hom_app_f, Int.reduceMul,
    Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg,
    Preadditive.neg_comp, neg_neg]
  erw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  change ((mappingCone ((s • 𝟙 K)⟦(1 : ℤ)⟧')).XIsoOfEq
      (by omega : q = q + 1 + -1)).hom ≫
      (((mappingCone.shiftIso (s • 𝟙 K) 1).inv.f (q + 1 + -1) ≫
        ((mappingCone (s • 𝟙 K)).XIsoOfEq
          (by omega : q + 1 + -1 + 1 = q + 1 + 1 + -1)).hom) ≫
        ((mappingCone (s • 𝟙 K)).XIsoOfEq
          (by omega : q + 1 + 1 + -1 = q + 1)).hom) = _
  simp only [Category.assoc]
  erw [← HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  change (mappingCone.shiftIso (s • 𝟙 K) 1).inv.f q ≫
      ((mappingCone (s • 𝟙 K)).XIsoOfEq
        (by omega : q + 1 = q + 1 + -1 + 1)).hom ≫
      ((mappingCone (s • 𝟙 K)).XIsoOfEq
        (by omega : q + 1 + -1 + 1 = q + 1 + 1 + -1)).hom ≫
      ((mappingCone (s • 𝟙 K)).XIsoOfEq
        (by omega : q + 1 + 1 + -1 = q + 1)).hom = _
  simp only [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  erw [Category.comp_id]

private theorem cochainShiftOne_second (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    (cochainShiftOne s K).f q ≫ second (s • 𝟙 K) (q + 1) =
      second (s • 𝟙 (K⟦(1 : ℤ)⟧)) q := by
  have hs : (s • 𝟙 K)⟦(1 : ℤ)⟧' = s • 𝟙 (K⟦(1 : ℤ)⟧) := by simp
  have h := cochainShiftOne_standard s K
  cases hs
  rw [eq_of_heq h]
  exact shift_inv_second s K q

private theorem cochainShiftOne_first (s : R) (K : CochainComplex A ℤ) (q : ℤ) :
    (cochainShiftOne s K).f q ≫ first (s • 𝟙 K) (q + 1) =
      -(first (s • 𝟙 (K⟦(1 : ℤ)⟧)) q ≫
        (K.XIsoOfEq (by omega : q + 1 + 1 = (q + 1) + 1)).hom) := by
  have hs : (s • 𝟙 K)⟦(1 : ℤ)⟧' = s • 𝟙 (K⟦(1 : ℤ)⟧) := by simp
  have h := cochainShiftOne_standard s K
  cases hs
  rw [eq_of_heq h]
  change _ = -(first ((s • 𝟙 K)⟦(1 : ℤ)⟧') q ≫ 𝟙 (K.X (q + 1 + 1)))
  erw [Category.comp_id]
  exact shift_inv_first s K q

private theorem cone_boundary_component {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (q : ℤ) : (mappingCone.triangle f).mor₃.f q = -first f q := by
  apply mappingCone.ext_from f (q + 1) q rfl
  · simp [first, shiftFunctorObjXIso]
  · simp [first]

private theorem interchange_boundary (s : R) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) :
    (cochain s).map (mappingCone.triangle f).mor₃ ≫ cochainShiftOne s K =
      (interchangeIso s f).hom ≫ (mappingCone.triangle ((cochain s).map f)).mor₃ := by
  ext q : 1
  simp only [HomologicalComplex.comp_f, interchangeIso_hom_f]
  apply cone_ext (s • 𝟙 K) (q + 1)
  · simp only [Category.assoc, cochainShiftOne_first, Preadditive.comp_neg,
      cone_boundary_component, Preadditive.neg_comp, interchange_first_first,
      neg_neg]
    erw [scalar_map_first_assoc s (mappingCone.triangle f).mor₃ q]
    simp only [cone_boundary_component, Preadditive.comp_neg, Preadditive.neg_comp,
      neg_neg]
    change first (s • 𝟙 (mappingCone f)) q ≫ first f (q + 1) ≫ 𝟙 _ = _
    rw [Category.comp_id]
  · simp only [Category.assoc, cochainShiftOne_second,
      cone_boundary_component, Preadditive.comp_neg,
      Preadditive.neg_comp, interchange_first_second]
    erw [scalar_map_second s (mappingCone.triangle f).mor₃ q]
    simp only [mappingCone.triangle_obj₃, cone_boundary_component, Preadditive.comp_neg]

private noncomputable def interchangeTriangleIso (s : R)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    let := cochainCommShift (A := A) s
    (cochain s).mapTriangle.obj (mappingCone.triangle f) ≅
      mappingCone.triangle ((cochain s).map f) := by
  let := cochainCommShift (A := A) s
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (interchangeIso s f) ?_ ?_ ?_
  · change (cochain s).map f ≫ 𝟙 _ = 𝟙 _ ≫ (cochain s).map f
    simp
  · change (cochain s).map (mappingCone.inr f) ≫ (interchangeIso s f).hom =
      𝟙 _ ≫ mappingCone.inr ((cochain s).map f)
    rw [Category.id_comp]
    exact interchange_inclusion s f
  · dsimp only [Functor.mapTriangle, Triangle.mk, Iso.refl_hom]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← cochainShiftOne_eq]
    exact interchange_boundary s f

variable [HasDerivedCategory.{w} A]

private noncomputable def derivedCoconeComparison (s : R) :
    cocone (A := A) s ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (derived s ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ)) :=
  Functor.isoWhiskerRight (coconeIso s) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.Q.commShiftIso (-1 : ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (comparison s).symm _ ≪≫ Functor.associator _ _ _

private noncomputable def derivedAdjunction (s : R) :
    (derived (A := A) s ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ)) ⊣ derived s := by
  let : CatCommSq (cocone (A := A) s) DerivedCategory.Q DerivedCategory.Q
      (derived s ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ)) := ⟨derivedCoconeComparison s⟩
  let : CatCommSq (cochain (A := A) s) DerivedCategory.Q DerivedCategory.Q (derived s) :=
    ⟨(comparison s).symm⟩
  exact (cochainAdjunction s).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _

@[instance_reducible]
private noncomputable def derivedCommShift (s : R) :
    (derived (A := A) s).CommShift ℤ := by
  let := cochainCommShift (A := A) s
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (cochain s ⋙ DerivedCategory.Q) (derived s) := ⟨comparison s⟩
  exact Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) ℤ (cochain s ⋙ DerivedCategory.Q) (derived s)

private theorem derived_triangulated (s : R) :
    let := derivedCommShift (A := A) s
    (derived (A := A) s).IsTriangulated := by
  let := cochainCommShift (A := A) s
  let := derivedCommShift (A := A) s
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (cochain s ⋙ DerivedCategory.Q) (derived s) := ⟨comparison s⟩
  have : NatTrans.CommShift (comparison (A := A) s).hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) ℤ (cochain s ⋙ DerivedCategory.Q) (derived s)
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨K, L, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  apply CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished ((cochain s).map f)) _
  exact (derived s).mapTriangle.mapIso e ≪≫
    (Functor.mapTriangleCompIso DerivedCategory.Q (derived s)).symm.app _ ≪≫
    (Functor.mapTriangleIso (comparison s)).app _ ≪≫
    (Functor.mapTriangleCompIso (cochain s) DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (interchangeTriangleIso s f)

private theorem derived_products (s : R) :
    PreservesLimitsOfShape (Discrete ℕ) (derived (A := A) s) :=
  (derivedAdjunction s).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- The localized two-term scalar cone is exact and preserves countable products.
Source: blueprint DVR effectivity proof, bounded-free tensor paragraph; Stacks 06YS,
0941. (blueprint: lem-coef-linear-scalar-cone-exact-products).

Proof: on complexes the functor is tensor with the two-term free scalar complex,
using the scalar action of R. Its degree-q object is X^(q+1) plus X^q.
Interchanging the two cone directions, with a minus sign on their doubly shifted
summand, identifies its value on a mapping-cone triangle with the triangle of the
diagonal cone map. This comparison commutes with the signed shift isomorphisms
and their addition cocycle, so it induces an exact functor on the homotopy
category. The proved quasi-isomorphism invariance descends it to localization.
The two-term scalar complex has a two-term dual: its evaluation and coevaluation
are the identity on matching scalar coordinates, with the tensor differential
sign on the shifted one. The triangle identities hold separately on the two
coordinates. Equivalently, the Hom-complex matrix formula identifies maps out of
one scalar cone with maps into the shifted dual scalar cone. This yields a
cochain adjunction, compatible with homotopies; both functors preserve
quasi-isomorphisms, so it descends through localization. The localized scalar
cone is consequently also a right adjoint and preserves every existing product.
No regularity of s, boundedness of X, or exactness of ordinary products is needed.
At s=0 it is identity plus shift; at an invertible s its values are contractible. -/
theorem exact_products
    {R : Type r} [Ring R] {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
    [HasDerivedCategory.{w} A] (s : R) :
    ∃ h : (derived (A := A) s).CommShift ℤ,
      letI := h
      (derived (A := A) s).IsTriangulated ∧
      PreservesLimitsOfShape (Discrete ℕ) (derived (A := A) s) := by
  exact ⟨derivedCommShift s, derived_triangulated s, derived_products s⟩

end CochainComplex.LinearScalarCone
