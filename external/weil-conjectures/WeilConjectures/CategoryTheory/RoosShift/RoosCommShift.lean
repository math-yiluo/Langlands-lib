/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
public import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
/-! # Coherent shifts of the native Roos functor

Tower evaluation and adjacent transitions use arbitrary target categories.
The Roos construction uses the additive structure and countable products.

Source: Stacks Project, Tags 011G, 014E and 08TC.
(blueprint: lem-weil-roos-comm-shift)
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe a b s v
private theorem cocone_zeroSecond {A : Type*} [Category A] [Abelian A]
    {M K L : CochainComplex A ℤ} (φ : K ⟶ L) (b : M ⟶ CochainComplex.mappingCocone φ)
    (j : ℤ)
    (hz : b.f j ≫ (CochainComplex.mappingCocone.snd φ).v j (j - 1) (by omega) = 0) :
    b.f j = (b ≫ CochainComplex.mappingCocone.fst φ).f j ≫
      (CochainComplex.mappingCocone.inl φ).v j j (by omega) := by
  calc
    b.f j = b.f j ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = b.f j ≫ ((CochainComplex.mappingCocone.fst φ).f j ≫
          (CochainComplex.mappingCocone.inl φ).v j j (by omega) +
        (CochainComplex.mappingCocone.snd φ).v j (j - 1) (by omega) ≫
          (CochainComplex.mappingCocone.inr φ).1.v (j - 1) j (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X]
    _ = _ := by
      simp only [Preadditive.comp_add, ← Category.assoc, HomologicalComplex.comp_f]
      rw [hz, zero_comp, add_zero]

private theorem cocone_chainShift {A S : Type*} [Category A] [Abelian A]
    [Category S] [HasShift S ℤ]
    (T F : S ⥤ CochainComplex A ℤ) [F.CommShift ℤ]
    (τ : F ⟶ F) [NatTrans.CommShift τ ℤ]
    (b : T ⟶ SignedCoconeShift.coconeFunctor F F τ)
    (hz : ∀ (P : S) (j : ℤ), (b.app P).f j ≫
      (CochainComplex.mappingCocone.snd (τ.app P)).v j (j - 1) (by omega) = 0)
    (P : S) (m : ℤ) (a : T.obj (P⟦m⟧) ⟶ (T.obj P)⟦m⟧)
    (hf : a ≫
        (b.app P ≫ CochainComplex.mappingCocone.fst (τ.app P))⟦m⟧' =
      b.app (P⟦m⟧) ≫ CochainComplex.mappingCocone.fst (τ.app (P⟦m⟧)) ≫
        (F.commShiftIso m).hom.app P) :
    a ≫ (b.app P)⟦m⟧' =
      b.app (P⟦m⟧) ≫ (SignedCoconeShift.coconeFunctorShiftIso F F τ P m).hom := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  conv_lhs => rw [cocone_zeroSecond (τ.app P) (b.app P) (j + m) (hz P (j + m))]
  conv_rhs => rw [cocone_zeroSecond (τ.app (P⟦m⟧)) (b.app (P⟦m⟧)) j (hz _ j)]
  simp only [Category.assoc]
  rw [SignedCoconeShift.coconeFunctorShiftIso_inl F F τ P m j]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  have h := congrArg (fun f ↦ f.f j) hf
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at h
  simpa only [Category.assoc, HomologicalComplex.comp_f] using
    congrArg (fun f ↦ f ≫
      (CochainComplex.mappingCocone.inl (τ.app P)).v (j + m) (j + m) (by omega)) h

namespace CategoryTheory.RoosShift
section Levels
variable {D : Type a} [Category.{b} D] {T : Type s} [Category.{v} T]
  (K : T ⥤ (ℕᵒᵖ ⥤ D))

noncomputable abbrev levelFunctor (n : ℕ) : T ⥤ D :=
  K ⋙ (evaluation ℕᵒᵖ D).obj (op n)

def transition (n : ℕ) : levelFunctor K (n + 1) ⟶ levelFunctor K n where
  app X := (K.obj X).map (homOfLE (Nat.le_succ n)).op
  naturality _ _ f := ((K.map f).naturality (homOfLE (Nat.le_succ n)).op).symm
end Levels

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {S : Type s} [Category.{v} S] [HasShift S ℤ]
  (K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))

variable [∀ n, (levelFunctor K n).CommShift ℤ]
  [∀ n, NatTrans.CommShift (transition K n) ℤ]

noncomputable abbrev productFunctor := ProductShift.productFunctor (levelFunctor K)
@[instance_reducible]
noncomputable def productCommShift : (productFunctor K).CommShift ℤ :=
  ProductShift.productCommShift (levelFunctor K)

attribute [local instance] productCommShift

noncomputable def endomorphism : productFunctor K ⟶ productFunctor K where
  app X := towerTransitionEndomorphism
    (K := fun n ↦ (K.obj X).obj (op n)) (WeilConjectures.integralOperationsTowerStep (K.obj X))
  naturality _ _ f := (WeilConjectures.integralOperationsRoos_square (K.map f)).symm

omit [∀ n, NatTrans.CommShift (transition K n) ℤ]
  [∀ n, (levelFunctor K n).CommShift ℤ] [HasShift S ℤ] in
lemma endomorphism_π (X : S) (n : ℕ) :
    (endomorphism K).app X ≫ Limits.Pi.π (fun n ↦ (levelFunctor K n).obj X) n =
      Limits.Pi.π (fun n ↦ (levelFunctor K n).obj X) n -
        Limits.Pi.π (fun n ↦ (levelFunctor K n).obj X) (n + 1) ≫ (transition K n).app X := by
  exact (towerTransitionEndomorphism_eq_iff
    (K := fun n ↦ (levelFunctor K n).obj X)
    (WeilConjectures.integralOperationsTowerStep (K.obj X)) _).1 rfl n

theorem endomorphism_commShift : NatTrans.CommShift (endomorphism K) ℤ := by
  constructor
  intro m
  apply NatTrans.ext
  funext X
  change (ProductShift.productShiftIso (levelFunctor K) X m).hom ≫
      ((endomorphism K).app X)⟦m⟧' =
    (endomorphism K).app (X⟦m⟧) ≫ (ProductShift.productShiftIso (levelFunctor K) X m).hom
  apply ProductShift.productShift_hom_ext (levelFunctor K) X m
  intro n
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, endomorphism_π]
  rw [Category.assoc, ProductShift.productShiftIso_π (levelFunctor K) X m n]
  simp only [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_comp,
    Preadditive.comp_sub]
  rw [ProductShift.productShiftIso_π (levelFunctor K) X m n,
    ProductShift.productShiftIso_π_assoc (levelFunctor K) X m (n + 1)]
  conv_rhs => rw [← Category.assoc, endomorphism_π]
  rw [NatTrans.shift_app_comm]
  simp only [Preadditive.sub_comp, Category.assoc]

attribute [local instance] endomorphism_commShift

noncomputable abbrev roosFunctor := K ⋙ WeilConjectures.integralOperationsRoosFunctor

/-- The native strict Roos functor has the signed mapping-cocone shift.
Source: Stacks 011G, 014E, 08TC (blueprint: lem-weil-roos-comm-shift).
Proof: the level shifts identify products and conjugate the transition endomorphism.
Apply the signed cocone shift. Its zero and addition laws give coherence. -/
@[instance_reducible]
noncomputable def commShift : (roosFunctor K).CommShift ℤ := by
  change (SignedCoconeShift.coconeFunctor (productFunctor K)
    (productFunctor K) (endomorphism K)).CommShift ℤ
  exact SignedCoconeShift.coconeCommShift _ _ _

lemma commShift_inl (X : S) (m j : ℤ) :
    (CochainComplex.mappingCocone.inl ((endomorphism K).app (X⟦m⟧))).v j j (by omega) ≫
        ((Functor.commShiftIso (roosFunctor K) (self := commShift K) m).hom.app X).f j =
      (ProductShift.productShiftIso (levelFunctor K) X m).hom.f j ≫
        (CochainComplex.mappingCocone.inl ((endomorphism K).app X)).v
          (j + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso ((roosFunctor K).obj X)
          m j (j + m) rfl).inv := by
  exact SignedCoconeShift.coconeFunctorShiftIso_inl
    (productFunctor K) (productFunctor K) (endomorphism K) X m j

lemma commShift_inr (X : S) (m i j : ℤ) (h : i + 1 = j) :
    (CochainComplex.mappingCocone.inr ((endomorphism K).app (X⟦m⟧))).1.v i j h ≫
        ((Functor.commShiftIso (roosFunctor K) (self := commShift K) m).hom.app X).f j =
      m.negOnePow • ((ProductShift.productShiftIso (levelFunctor K) X m).hom.f i ≫
        (CochainComplex.mappingCocone.inr ((endomorphism K).app X)).1.v
          (i + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso ((roosFunctor K).obj X)
          m j (j + m) rfl).inv) := by
  exact SignedCoconeShift.coconeFunctorShiftIso_inr
    (productFunctor K) (productFunctor K) (endomorphism K) X m i j h

/-- The two coordinate equations for a native Roos shift and a fixed product comparison.
Source: Stacks 011G, 014E and 08TC (blueprint: lem-weil-roos-comm-shift). -/
def ConeFormula
    (productIso : ∀ (X : S) (m : ℤ),
      (∏ᶜ fun n ↦ (levelFunctor K n).obj (X⟦m⟧)) ≅
        (∏ᶜ fun n ↦ (levelFunctor K n).obj X)⟦m⟧)
    (eC : (roosFunctor K).CommShift ℤ) : Prop :=
  ∀ (X : S) (m : ℤ),
    (∀ j : ℤ,
      (CochainComplex.mappingCocone.inl ((endomorphism K).app (X⟦m⟧))).v j j (by omega) ≫
          ((Functor.commShiftIso (roosFunctor K) (self := eC) m).hom.app X).f j =
        (productIso X m).hom.f j ≫
          (CochainComplex.mappingCocone.inl ((endomorphism K).app X)).v
            (j + m) (j + m) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso ((roosFunctor K).obj X)
            m j (j + m) rfl).inv) ∧
    (∀ (i j : ℤ) (h : i + 1 = j),
      (CochainComplex.mappingCocone.inr ((endomorphism K).app (X⟦m⟧))).1.v i j h ≫
          ((Functor.commShiftIso (roosFunctor K) (self := eC) m).hom.app X).f j =
        m.negOnePow • ((productIso X m).hom.f i ≫
          (CochainComplex.mappingCocone.inr ((endomorphism K).app X)).1.v
            (i + m) (j + m) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso ((roosFunctor K).obj X)
            m j (j + m) rfl).inv))

/-- The constructed native shift satisfies its coordinate API for the canonical product shift.
Source: Stacks 011G and 014E (blueprint: lem-weil-roos-comm-shift).
Proof: substitute the prescribed product comparison and use the two inclusion formulas. -/
theorem commShift_formula
    (productIso : ∀ (X : S) (m : ℤ),
      (∏ᶜ fun n ↦ (levelFunctor K n).obj (X⟦m⟧)) ≅
        (∏ᶜ fun n ↦ (levelFunctor K n).obj X)⟦m⟧)
    (hproduct : ∀ X m, productIso X m = ProductShift.productShiftIso (levelFunctor K) X m) :
    ConeFormula K productIso (commShift K) := by
  intro X m
  rw [hproduct X m]
  exact ⟨commShift_inl K X m, commShift_inr K X m⟩

/-- A map with zero second coordinate commutes with the Roos shift when its first
coordinate commutes with the product shift.
Source: Stacks 011G and 08TC (blueprint: lem-weil-roos-comm-shift).
Proof: the two cocone projections determine a map. The first-coordinate hypothesis
identifies the first components. The signed second inclusion multiplies zero by a sign,
so the second components are both zero. -/
lemma chain_shift (T : S ⥤ CochainComplex A ℤ) (b : T ⟶ roosFunctor K)
    (hz : ∀ (X : S) (j : ℤ), (b.app X).f j ≫
      (CochainComplex.mappingCocone.snd ((endomorphism K).app X)).v j (j - 1) (by omega) = 0)
    (X : S) (m : ℤ) (a : T.obj (X⟦m⟧) ⟶ (T.obj X)⟦m⟧)
    (hf : a ≫ (b.app X ≫ CochainComplex.mappingCocone.fst
          ((endomorphism K).app X))⟦m⟧' =
      b.app (X⟦m⟧) ≫ CochainComplex.mappingCocone.fst ((endomorphism K).app (X⟦m⟧)) ≫
        (ProductShift.productShiftIso (levelFunctor K) X m).hom) :
    a ≫ (b.app X)⟦m⟧' = b.app (X⟦m⟧) ≫
      (Functor.commShiftIso (roosFunctor K) (self := commShift K) m).hom.app X := by
  exact cocone_chainShift T (productFunctor K) (endomorphism K) b hz X m a hf

end CategoryTheory.RoosShift
