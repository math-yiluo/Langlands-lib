/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Signed source shift for the sheaf Hom complex

Source: Stacks Project, sites-cohomology.tex, Tag 0A8X, section-hom-complexes.
(blueprint: lem-pur-hom-complex-shift-left).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private lemma homObjMap_neg_left
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (-f) g = -SheafOfModules.homObjMap f g := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (-f.val) ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val =
    -((PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val)
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (-((f.val.app _).hom x))) =
    -((g.val.app _).hom) ((φ.app W).hom ((f.val.app _).hom x))
  rw [map_neg, map_neg]

private lemma homObjMap_units_smul_left
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (r : ℤˣ) (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (r • f) g = r • SheafOfModules.homObjMap f g := by
  rcases Int.units_eq_one_or r with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, homObjMap_neg_left]

-- The dependent product projection formulas require repeated complex-index transport.
set_option backward.isDefEq.respectTransparency false in
/-- The signed reindexing for a source shift is natural in the target complex.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8X, section-hom-complexes;
the signed calculation is step 2 of the source-shift comparison.
(blueprint: lem-pur-hom-complex-shift-left).

Proof: In degree k the p-th component of the forward map is (-1)^(m*k)
times the input component p+m, with the index identifications
(L[m])^p = L^(p+m) and M^(p+k) = M^((p+m)+(k-m)).
Use the universal property of the product of internal Hom sheaves to define
this map. The inverse reindexes p to p-m and multiplies by the same scalar;
their composites are identities since the scalar squares to one. To check
the chain identity, project to each factor. The shifted source differential
has postcomposition coefficient (-1)^m and precomposition coefficient -(-1)^k.
The target has postcomposition coefficient 1 and precomposition coefficient
-(-1)^(k+m). The ratio of scalars in adjacent degrees is (-1)^m, giving
both identities. For degrees not adjacent both differentials vanish.
Postcomposition with any chain map commutes with the reindexing and scalars,
so these chain isomorphisms form a natural isomorphism. No boundedness or
injectivity is used. For m=0 the construction is the identity, for negative
m it uses the same integer identities, and zero complexes give zero products. -/
theorem homComplex_shift_left
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (m : ℤ) :
    Nonempty (((homComplexFunctor (R := R)).obj (op L) ⋙ shiftFunctor _ (-m)) ≅
      (homComplexFunctor (R := R)).obj (op (L⟦m⟧)))  := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  have hFπ := homComplex_projections_exists (R := R)
  generalize hF : homComplexFunctor (R := R) = F at hFπ ⊢
  obtain ⟨π, hπ₁, hπ₂, hπ₃⟩ := hFπ
  have hp (L M : CochainComplex A ℤ) (n : ℤ) := Classical.choice (hπ₁ L M n)
  let S := L⟦m⟧
  let K (M : CochainComplex A ℤ) := ((F.obj (op L)).obj M)⟦-m⟧
  let T (M : CochainComplex A ℤ) := (F.obj (op S)).obj M
  let a (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ⟶ (T M).X n :=
    Fan.IsLimit.lift (hp S M n) (fun p ↦
      (m * n).negOnePow • π L M (n - m) (p + m) (p + n) (by omega))
  have ha (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q) :
      a M n ≫ π S M n p q h =
        (m * n).negOnePow • π L M (n - m) (p + m) q (by omega) := by
    subst q
    exact Fan.IsLimit.fac (hp S M n) _ p
  let b (M : CochainComplex A ℤ) (n : ℤ) : (T M).X n ⟶ (K M).X n :=
    Fan.IsLimit.lift (hp L M (n - m)) (fun p ↦
      (m * n).negOnePow • (π S M n (p - m) (p + (n - m)) (by omega) ≫
        SheafOfModules.homObjMap (R := R)
          (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)))
  have hb (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + (n - m) = q) :
      b M n ≫ π L M (n - m) p q h =
        (m * n).negOnePow • (π S M n (p - m) q (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)) := by
    subst q
    exact Fan.IsLimit.fac (hp L M (n - m)) _ p
  have hπeq (Lc M : CochainComplex A ℤ) (n p p' q : ℤ)
      (h : p' = p) (hq : p + n = q) :
      π Lc M n p' q (by omega) ≫
          SheafOfModules.homObjMap (R := R) (Lc.XIsoOfEq h).inv (𝟙 _) = π Lc M n p q hq := by
    subst p'
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      SheafOfModules.homObjMap_id (R := R), Category.comp_id]
  have hab (M : CochainComplex A ℤ) (n : ℤ) : a M n ≫ b M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp L M (n - m))
    intro p
    change (a M n ≫ b M n) ≫ π L M (n - m) p (p + (n - m)) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    conv_lhs =>
      rw [Category.assoc]
      rhs
      rw [hb M n p (p + (n - m)) rfl]
    conv_lhs =>
      rw [Linear.comp_units_smul]
      rhs
      rw [← Category.assoc]
      lhs
      rw [ha M n (p - m) (p + (n - m)) (by omega)]
    simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
    change _ = π L M (n - m) p (p + (n - m)) rfl
    exact hπeq L M (n - m) p (p - m + m) (p + (n - m)) (by omega) rfl
  have hba (M : CochainComplex A ℤ) (n : ℤ) : b M n ≫ a M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp S M n)
    intro p
    change (b M n ≫ a M n) ≫ π S M n p (p + n) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    conv_lhs =>
      rw [Category.assoc]
      rhs
      rw [ha M n p (p + n) rfl]
    conv_lhs =>
      rw [Linear.comp_units_smul]
      rhs
      rw [hb M n (p + m) (p + n) (by omega)]
    simp only [smul_smul, Int.units_mul_self, one_smul]
    change _ = π S M n p (p + n) rfl
    exact hπeq S M n p (p + m - m) (p + n) (by omega) rfl
  let e (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ≅ (T M).X n :=
    ⟨a M n, b M n, hab M n, hba M n⟩
  have hm (Lc M N : CochainComplex A ℤ) (f : M ⟶ N)
      (n p q : ℤ) (h : p + n = q) :
      ((F.obj (op Lc)).map f).f n ≫ π Lc N n p q h =
        π Lc M n p q h ≫ SheafOfModules.homObjMap (R := R) (𝟙 (Lc.X p)) (f.f q) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ₃ Lc Lc M N (𝟙 Lc) f n p q h
  have hc (M : CochainComplex A ℤ) (n k : ℤ) (h : n + 1 = k) :
      (e M n).hom ≫ (T M).d n k = (K M).d n k ≫ (e M k).hom := by
    subst k
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a ha ⊢
    apply Fan.IsLimit.hom_ext (hp S M (n + 1))
    intro p
    change (a M n ≫ (T M).d n (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl =
      (((-m).negOnePow • ((F.obj (op L)).obj M).d (n - m) (n + 1 - m)) ≫
        a M (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl
    -- Focus on each projection composite so matching does not unfold the product lifts.
    conv_lhs =>
      rw [Category.assoc]
      rhs
      rw [hπ₂ S M n (n + 1) p (p + (n + 1)) (p + n) (p + 1)
        rfl rfl rfl (by omega)]
    conv_lhs => rw [Preadditive.comp_sub]
    conv_lhs =>
      lhs
      rw [← Category.assoc]
      lhs
      rw [ha M n p (p + n) rfl]
    conv_lhs =>
      rhs
      rw [Linear.comp_units_smul]
      rhs
      rw [← Category.assoc]
      lhs
      rw [ha M n (p + 1) (p + (n + 1)) (by omega)]
    conv_rhs =>
      rw [Category.assoc]
      rhs
      rw [ha M (n + 1) p (p + (n + 1)) rfl]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
    conv_rhs =>
      rhs
      rw [hπ₂ L M (n - m) (n + 1 - m) (p + m) (p + (n + 1)) (p + n) (p + 1 + m)
        (by omega) (by omega) (by omega) (by omega)]
    simp only [S, CochainComplex.shiftFunctor_obj_d', homObjMap_units_smul_left,
      Linear.comp_units_smul, smul_sub, smul_smul,
      Int.negOnePow_neg, Int.negOnePow_sub]
    have hs : (m * (n + 1)).negOnePow = (m * n).negOnePow * m.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    simp only [hs, mul_assoc, Int.units_mul_self, mul_one]
    conv_lhs =>
      rhs
      lhs
      rw [mul_left_comm n.negOnePow (m * n).negOnePow m.negOnePow]
    rfl
  refine ⟨NatIso.ofComponents (fun M ↦
    HomologicalComplex.Hom.isoOfComponents (e M) (hc M)) ?_⟩
  intro M N f
  apply HomologicalComplex.hom_ext
  intro n
  change ((F.obj (op L)).map f).f (n - m) ≫ a N n =
    a M n ≫ ((F.obj (op S)).map f).f n
  apply Fan.IsLimit.hom_ext (hp S N n)
  intro p
  change (((F.obj (op L)).map f).f (n - m) ≫ a N n) ≫
      π S N n p (p + n) rfl =
    (a M n ≫ ((F.obj (op S)).map f).f n) ≫ π S N n p (p + n) rfl
  -- Use naturality only at the selected factor of the product.
  conv_lhs =>
    rw [Category.assoc]
    rhs
    rw [ha N n p (p + n) rfl]
  conv_lhs =>
    rw [Linear.comp_units_smul]
    rhs
    rw [hm L M N f (n - m) (p + m) (p + n) (by omega)]
  conv_rhs =>
    rw [Category.assoc]
    rhs
    rw [hm S M N f n p (p + n) rfl]
  conv_rhs =>
    rw [← Category.assoc]
    lhs
    rw [ha M n p (p + n) rfl]
  rw [Linear.units_smul_comp]
  rfl

end CategoryTheory
