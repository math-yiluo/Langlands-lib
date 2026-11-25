/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Right shifts of the Hom complex
Source: Stacks Project, Cohomology on Sites, Sections 21.34--21.35.
(blueprint: lem-pur-hom-complex-shift-right).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

private noncomputable def productComparisonIso
    {D : Type*} [Category D] {ι : Type*} {A B : ι → D}
    (s : Limits.Fan A) (t : Limits.Fan B) (hs : Limits.IsLimit s) (ht : Limits.IsLimit t)
    (e : ∀ i, A i ≅ B i) : s.pt ≅ t.pt where
  hom := Limits.Fan.IsLimit.lift ht (fun i ↦ s.proj i ≫ (e i).hom)
  inv := Limits.Fan.IsLimit.lift hs (fun i ↦ t.proj i ≫ (e i).inv)
  hom_inv_id := by
    apply Limits.Fan.IsLimit.hom_ext hs
    intro i
    simp
  inv_hom_id := by
    apply Limits.Fan.IsLimit.hom_ext ht
    intro i
    simp

private lemma productComparisonIso_hom_proj
    {D : Type*} [Category D] {ι : Type*} {A B : ι → D}
    (s : Limits.Fan A) (t : Limits.Fan B) (hs : Limits.IsLimit s) (ht : Limits.IsLimit t)
    (e : ∀ i, A i ≅ B i) (i : ι) :
    (productComparisonIso s t hs ht e).hom ≫ t.proj i = s.proj i ≫ (e i).hom :=
  Limits.Fan.IsLimit.fac ht _ i

private lemma homObjMap_units_smul_right
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') (a : ℤˣ) :
    SheafOfModules.homObjMap (R := R) f (a • g) =
      a • SheafOfModules.homObjMap f g := by
  apply SheafOfModules.hom_ext
  obtain ha | ha := Int.units_eq_one_or a
  · subst a
    simp
  · subst a
    simp only [Units.neg_smul, one_smul]
    ext X φ
    rfl

private noncomputable def homTargetIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (A B B' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (e : B ≅ B') :
    SheafOfModules.homObj (R := R) A B ≅ SheafOfModules.homObj (R := R) A B' where
  hom := SheafOfModules.homObjMap (R := R) (𝟙 A) e.hom
  inv := SheafOfModules.homObjMap (R := R) (𝟙 A) e.inv
  hom_inv_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R)]
    simp
  inv_hom_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R)]
    simp

private lemma shiftSign_sub {A : Type*} [AddCommGroup A]
    (a b : A) (k n : ℤ) :
    n.negOnePow • a - k.negOnePow • b =
      n.negOnePow • (a - (k + n).negOnePow • b) := by
  rw [smul_sub n.negOnePow a ((k + n).negOnePow • b),
    smul_smul n.negOnePow (k + n).negOnePow b, Int.negOnePow_add,
    mul_left_comm, Int.units_mul_self, mul_one]

-- The dependent product projections require elaborating the Hom-complex specification.
set_option backward.isDefEq.respectTransparency true in
/-- The Hom-complex bifunctor commutes with shifts in its second complex.
Source: Stacks Project, sites-cohomology.tex, Sections 21.34 and 21.35
(Tags 0A8X and 08JA).
(blueprint: lem-pur-hom-complex-shift-right).
Proof: In degree k both sides are products indexed by p of internal Hom from
L^p to M^(p+k+n). Use the product universal property and the shift degree
isomorphisms to identify these products. The inverse uses the inverse degree
isomorphisms. The shifted differential has postcomposition coefficient
(-1)^n and precomposition coefficient -(-1)^(k+n+n) = -(-1)^k;
the Hom differential with shifted target has precisely these coefficients.
The product projections therefore verify the chain-map equation, and the
inverse equations hold projectionwise. Precomposition in L and postcomposition
in M commute with the degree identifications, giving naturality in both complexes.
The formula works for all integer shifts, unbounded complexes, and zero objects. -/
theorem homComplex_shift_right
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (n : ℤ) :
    Nonempty (
      Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R)) ⋙
        shiftFunctor _ n ≅
      (𝟭 _).prod (shiftFunctor _ n) ⋙
        Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R))) := by
  have hFπ := homComplex_projections_exists (C := C) (J := J) (R := R)
  generalize homComplexFunctor (C := C) (J := J) (R := R) = F at hFπ ⊢
  obtain ⟨π, hprod, hd, hmap⟩ := hFπ
  let e (L M : _) (k : ℤ) :
      ((F.obj (op L)).obj M).X (k + n) ≅ ((F.obj (op L)).obj (M⟦n⟧)).X k :=
    productComparisonIso
      (Limits.Fan.mk (((F.obj (op L)).obj M).X (k + n))
        (fun p ↦ π L M (k + n) p (p + (k + n)) rfl))
      (Limits.Fan.mk (((F.obj (op L)).obj (M⟦n⟧)).X k)
        (fun p ↦ π L (M⟦n⟧) k p (p + k) rfl))
      (hprod L M (k + n)).some (hprod L (M⟦n⟧) k).some
      (fun p ↦ homTargetIso (R := R) (L.X p) _ _
        (M.shiftFunctorObjXIso n (p + k) (p + (k + n)) (by omega)).symm)
  have hπinv (L M : _) (k p q q' : ℤ) (hpq : p + k = q) (h : q' = q) :
      π L M k p q hpq ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (M.XIsoOfEq h).inv =
      π L M k p q' (by omega) := by
    subst q'
    simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      SheafOfModules.homObjMap_id] using Category.comp_id (π L M k p q hpq)
  have he (L M : _) (k p q : ℤ) (hpq : p + k = q) :
      (e L M k).hom ≫ π L (M⟦n⟧) k p q hpq =
        π L M (k + n) p (q + n) (by omega) := by
    subst q
    dsimp only [e]
    change (productComparisonIso _ _ _ _ _).hom ≫
      (Limits.Fan.mk (((F.obj (op L)).obj (M⟦n⟧)).X k)
        (fun p ↦ π L (M⟦n⟧) k p (p + k) rfl)).proj p = _
    rw [productComparisonIso_hom_proj]
    change π L M (k + n) p (p + (k + n)) rfl ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (L.X p))
        (M.XIsoOfEq (show (p + k) + n = p + (k + n) by omega)).inv = _
    exact hπinv L M (k + n) p (p + (k + n)) ((p + k) + n) rfl (by omega)
  refine ⟨NatIso.ofComponents (fun X ↦
    HomologicalComplex.Hom.isoOfComponents (e X.1.unop X.2) ?_) ?_⟩
  · intro k l hkl
    have hkl' : k + 1 = l := hkl
    change (e X.1.unop X.2 k).hom ≫ ((F.obj X.1).obj (X.2⟦n⟧)).d k l =
      (n.negOnePow • ((F.obj X.1).obj X.2).d (k + n) (l + n)) ≫
        (e X.1.unop X.2 l).hom
    apply Limits.Fan.IsLimit.hom_ext (hprod X.1.unop (X.2⟦n⟧) l).some
    intro p
    change ((e X.1.unop X.2 k).hom ≫ ((F.obj X.1).obj (X.2⟦n⟧)).d k l) ≫
      π X.1.unop (X.2⟦n⟧) l p (p + l) rfl =
      ((n.negOnePow • ((F.obj X.1).obj X.2).d (k + n) (l + n)) ≫
        (e X.1.unop X.2 l).hom) ≫ π X.1.unop (X.2⟦n⟧) l p (p + l) rfl
    -- Focus each rewrite to avoid unfolding unrelated morphisms while matching projections.
    conv_lhs =>
      rw [Category.assoc]
      rhs
      rw [hd X.1.unop (X.2⟦n⟧) k l p (p + l) (p + k) (p + 1)
        hkl' rfl rfl (by omega)]
    conv_lhs => rw [Preadditive.comp_sub]
    conv_lhs =>
      rhs
      rw [Linear.comp_units_smul]
    conv_lhs =>
      lhs
      rw [← Category.assoc]
      lhs
      rw [he X.1.unop X.2 k p (p + k) rfl]
    conv_lhs =>
      rhs
      rhs
      rw [← Category.assoc]
      lhs
      rw [he X.1.unop X.2 k (p + 1) (p + l) (by omega)]
    conv_rhs =>
      rw [Category.assoc]
      rhs
      rw [he X.1.unop X.2 l p (p + l) rfl]
    conv_rhs =>
      rw [Linear.units_smul_comp]
      rhs
      rw [hd X.1.unop X.2 (k + n) (l + n) p ((p + l) + n) ((p + k) + n) (p + 1)
          (by omega) (by omega) (by omega) (by omega)]
    simp only [CochainComplex.shiftFunctor_obj_d']
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    conv_lhs =>
      lhs
      rhs
      rw [homObjMap_units_smul_right (R := R) (𝟙 (X.1.unop.X p))
        (X.2.d ((p + k) + n) ((p + l) + n)) n.negOnePow]
    conv_lhs =>
      lhs
      rw [Linear.comp_units_smul]
    let a := π X.1.unop X.2 (k + n) p ((p + k) + n) (by omega) ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (X.1.unop.X p))
        (X.2.d ((p + k) + n) ((p + l) + n))
    let b := π X.1.unop X.2 (k + n) (p + 1) ((p + l) + n) (by omega) ≫
      SheafOfModules.homObjMap (R := R) (X.1.unop.d p (p + 1))
        (𝟙 (X.2.X ((p + l) + n)))
    change n.negOnePow • a - k.negOnePow • b =
      n.negOnePow • (a - (k + n).negOnePow • b)
    exact shiftSign_sub a b k n
  · intro X Y f
    apply HomologicalComplex.hom_ext
    intro k
    apply Limits.Fan.IsLimit.hom_ext (hprod Y.1.unop (Y.2⟦n⟧) k).some
    intro p
    change
      (((F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2).f (k + n) ≫
        (e Y.1.unop Y.2 k).hom) ≫ π Y.1.unop (Y.2⟦n⟧) k p (p + k) rfl =
      ((e X.1.unop X.2 k).hom ≫
        ((F.map f.1).app (X.2⟦n⟧) ≫ (F.obj Y.1).map (f.2⟦n⟧')).f k) ≫
        π Y.1.unop (Y.2⟦n⟧) k p (p + k) rfl
    conv_lhs =>
      rw [Category.assoc]
      rhs
      rw [he Y.1.unop Y.2 k p (p + k) rfl]
    conv_lhs =>
      erw [hmap X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 (k + n) p ((p + k) + n)
        (by omega)]
    conv_rhs =>
      rw [Category.assoc]
      rhs
      erw [hmap X.1.unop Y.1.unop (X.2⟦n⟧) (Y.2⟦n⟧) f.1.unop (f.2⟦n⟧') k p (p + k) rfl]
    conv_rhs =>
      rw [← Category.assoc]
      lhs
      rw [he X.1.unop X.2 k p (p + k) rfl]
    rfl

end CategoryTheory
