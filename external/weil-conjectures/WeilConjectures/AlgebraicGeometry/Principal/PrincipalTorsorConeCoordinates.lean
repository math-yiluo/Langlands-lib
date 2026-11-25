/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates

/-!
# Coordinates on the shifted mapping cone in every degree

For a morphism `r: A ⟶ B` of integer cochain complexes of abelian groups, an element of
degree `n` of `(mappingCone r)⟦-1⟧` is a pair consisting of an element of `A.X n` and an
element of `B.X m`, where `m + 1 = n`. This file records the two coordinates, the
construction of an element from its coordinates, and the formulas for the differential and
for the functoriality of `relativeFiberMap` in these coordinates.

## References

* Stacks Project, Tag 0G71 (mapping fibre of a morphism of complexes)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

namespace AlgebraicGeometry.Etale.ShiftedCone

variable {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r : A ⟶ B)

/-- The first coordinate of an element of degree `n` of the shifted cone. -/
def fst (n m : ℤ) (h : m + 1 = n) : ((mappingCone r)⟦(-1 : ℤ)⟧).X n ⟶ A.X n :=
  ((mappingCone r).shiftFunctorObjXIso (-1) n m (by omega)).hom ≫
    (mappingCone.fst r).1.v m n h

/-- The second coordinate of an element of degree `n` of the shifted cone. -/
def snd (n m : ℤ) (h : m + 1 = n) : ((mappingCone r)⟦(-1 : ℤ)⟧).X n ⟶ B.X m :=
  ((mappingCone r).shiftFunctorObjXIso (-1) n m (by omega)).hom ≫
    (mappingCone.snd r).v m m (add_zero m)

/-- The inclusion of the first summand into the shifted cone. -/
def inl (n m : ℤ) (h : m + 1 = n) : A.X n ⟶ ((mappingCone r)⟦(-1 : ℤ)⟧).X n :=
  (mappingCone.inl r).v n m (by omega) ≫
    ((mappingCone r).shiftFunctorObjXIso (-1) n m (by omega)).inv

/-- The inclusion of the second summand into the shifted cone. -/
def inr (n m : ℤ) (h : m + 1 = n) : B.X m ⟶ ((mappingCone r)⟦(-1 : ℤ)⟧).X n :=
  (mappingCone.inr r).f m ≫ ((mappingCone r).shiftFunctorObjXIso (-1) n m (by omega)).inv

@[reassoc (attr := simp)]
lemma inl_fst (n m : ℤ) (h : m + 1 = n) : inl r n m h ≫ fst r n m h = 𝟙 _ := by
  simp [inl, fst]

@[reassoc (attr := simp)]
lemma inl_snd (n m : ℤ) (h : m + 1 = n) : inl r n m h ≫ snd r n m h = 0 := by
  simp [inl, snd]

@[reassoc (attr := simp)]
lemma inr_fst (n m : ℤ) (h : m + 1 = n) : inr r n m h ≫ fst r n m h = 0 := by
  simp [inr, fst]

@[reassoc (attr := simp)]
lemma inr_snd (n m : ℤ) (h : m + 1 = n) : inr r n m h ≫ snd r n m h = 𝟙 _ := by
  simp [inr, snd]

lemma fst_inl_add_snd_inr (n m : ℤ) (h : m + 1 = n) :
    fst r n m h ≫ inl r n m h + snd r n m h ≫ inr r n m h = 𝟙 _ := by
  simp only [fst, inl, snd, inr, Category.assoc]
  rw [← Category.assoc ((mappingCone.fst r).1.v m n h),
    ← Category.assoc ((mappingCone.snd r).v m m (add_zero m)), ← Preadditive.comp_add,
    ← Preadditive.add_comp, mappingCone.id_X r m n h]
  simp

/-- The element of the shifted cone with prescribed coordinates. -/
def mk (n m : ℤ) (h : m + 1 = n) (a : A.X n) (b : B.X m) : ((mappingCone r)⟦(-1 : ℤ)⟧).X n :=
  inl r n m h a + inr r n m h b

@[simp]
lemma fst_mk (n m : ℤ) (h : m + 1 = n) (a : A.X n) (b : B.X m) :
    fst r n m h (mk r n m h a b) = a := by
  rw [mk, map_add, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    inl_fst, inr_fst]
  simp

@[simp]
lemma snd_mk (n m : ℤ) (h : m + 1 = n) (a : A.X n) (b : B.X m) :
    snd r n m h (mk r n m h a b) = b := by
  rw [mk, map_add, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    inl_snd, inr_snd]
  simp

lemma eq_mk (n m : ℤ) (h : m + 1 = n) (x : ((mappingCone r)⟦(-1 : ℤ)⟧).X n) :
    x = mk r n m h (fst r n m h x) (snd r n m h x) := by
  have hx := ConcreteCategory.congr_hom (fst_inl_add_snd_inr r n m h) x
  simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, ConcreteCategory.comp_apply,
    AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at hx
  exact hx.symm

lemma ext {n m : ℤ} (h : m + 1 = n) {x y : ((mappingCone r)⟦(-1 : ℤ)⟧).X n}
    (h₁ : fst r n m h x = fst r n m h y) (h₂ : snd r n m h x = snd r n m h y) : x = y := by
  rw [eq_mk r n m h x, eq_mk r n m h y, h₁, h₂]

private lemma shift_d (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n') :
    ((mappingCone r)⟦(-1 : ℤ)⟧).d n n' =
      -(((mappingCone r).shiftFunctorObjXIso (-1) n m (by omega)).hom ≫
        (mappingCone r).d m n ≫
        ((mappingCone r).shiftFunctorObjXIso (-1) n' n (by omega)).inv) := by
  rw [shiftFunctor_obj_d']
  simp only [shiftFunctorObjXIso, d_comp_XIsoOfEq_inv, XIsoOfEq_hom_comp_d, Int.reduceNeg,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]

/-- The first coordinate of the differential is the differential of the first coordinate. -/
@[reassoc]
lemma d_fst (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n') :
    ((mappingCone r)⟦(-1 : ℤ)⟧).d n n' ≫ fst r n' n h' = fst r n m h ≫ A.d n n' := by
  rw [shift_d r n n' m h h']
  simp only [fst, Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc,
    mappingCone.d_fst_v r m n n' h h']
  simp

/-- The second coordinate of the differential, in the unsigned convention. -/
@[reassoc]
lemma d_snd (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n') :
    ((mappingCone r)⟦(-1 : ℤ)⟧).d n n' ≫ snd r n' n h' =
      -(fst r n m h ≫ r.f n + snd r n m h ≫ B.d m n) := by
  rw [shift_d r n n' m h h']
  simp only [fst, snd, Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc,
    mappingCone.d_snd_v r m n h]
  simp


lemma d_fst_apply (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n')
    (x : ((mappingCone r)⟦(-1 : ℤ)⟧).X n) :
    fst r n' n h' (((mappingCone r)⟦(-1 : ℤ)⟧).d n n' x) = A.d n n' (fst r n m h x) := by
  rw [← ConcreteCategory.comp_apply, d_fst r n n' m h h', ConcreteCategory.comp_apply]

lemma d_snd_apply (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n')
    (x : ((mappingCone r)⟦(-1 : ℤ)⟧).X n) :
    snd r n' n h' (((mappingCone r)⟦(-1 : ℤ)⟧).d n n' x) =
      -(r.f n (fst r n m h x) + B.d m n (snd r n m h x)) := by
  rw [← ConcreteCategory.comp_apply, d_snd r n n' m h h']
  simp

section FiberMap

variable {A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r' : A' ⟶ B') (a : A ⟶ A')
  (b : B ⟶ B') (hc : a ≫ r' = r ≫ b)

private lemma coneMap_fst (n : ℤ) :
    (homotopyCofiber.mapArrowHom r r' (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk a b hc)).f n ≫ homotopyCofiber.fstX r' n (n + 1) rfl =
      homotopyCofiber.fstX r n (n + 1) rfl ≫ a.f (n + 1) := by
  dsimp only [homotopyCofiber.fstX]
  rw [← Category.assoc, coneMap_XIso]
  simp

private lemma cone_snd {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (i : ℤ) :
    (homotopyCofiber.XIsoBiprod r i (i + 1) rfl).hom ≫ biprod.snd =
      homotopyCofiber.sndX r i := by
  apply homotopyCofiber.ext_from_X r (i + 1) i rfl <;> simp

private lemma coneMap_snd (n : ℤ) :
    (homotopyCofiber.mapArrowHom r r' (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk a b hc)).f n ≫ homotopyCofiber.sndX r' n =
      homotopyCofiber.sndX r n ≫ b.f n := by
  rw [← cone_snd r' n, ← cone_snd r n, ← Category.assoc, coneMap_XIso]
  simp

/-- The map of shifted cones preserves the first coordinate. -/
@[reassoc]
lemma fiberMap_fst (n m : ℤ) (h : m + 1 = n) :
    (relativeFiberMap r r' a b hc).f n ≫ fst r' n m h = fst r n m h ≫ a.f n := by
  subst h
  simp only [relativeFiberMap, fst, shiftFunctor_map_f', shiftFunctorObjXIso, Category.assoc]
  erw [← Category.assoc, XIsoOfEq_hom_naturality, Category.assoc, coneMap_fst]
  rfl

/-- The map of shifted cones preserves the second coordinate. -/
@[reassoc]
lemma fiberMap_snd (n m : ℤ) (h : m + 1 = n) :
    (relativeFiberMap r r' a b hc).f n ≫ snd r' n m h = snd r n m h ≫ b.f m := by
  subst h
  simp only [relativeFiberMap, snd, shiftFunctor_map_f', shiftFunctorObjXIso, Category.assoc]
  erw [← Category.assoc, XIsoOfEq_hom_naturality, Category.assoc, coneMap_snd]
  rfl

lemma fiberMap_fst_apply (n m : ℤ) (h : m + 1 = n) (x : ((mappingCone r)⟦(-1 : ℤ)⟧).X n) :
    fst r' n m h ((relativeFiberMap r r' a b hc).f n x) = a.f n (fst r n m h x) := by
  rw [← ConcreteCategory.comp_apply, fiberMap_fst, ConcreteCategory.comp_apply]

lemma fiberMap_snd_apply (n m : ℤ) (h : m + 1 = n) (x : ((mappingCone r)⟦(-1 : ℤ)⟧).X n) :
    snd r' n m h ((relativeFiberMap r r' a b hc).f n x) = b.f m (snd r n m h x) := by
  rw [← ConcreteCategory.comp_apply, fiberMap_snd, ConcreteCategory.comp_apply]

end FiberMap

end AlgebraicGeometry.Etale.ShiftedCone
