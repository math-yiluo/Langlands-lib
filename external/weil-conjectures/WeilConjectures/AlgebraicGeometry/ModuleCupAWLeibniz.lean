/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupAWComponents

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.Abel

/-! # Signed Leibniz identity for the front/back components

Source: Banerjee, Tensor Structure on Smooth Motives, §1.1.4, p. 16.
(blueprint: lem-sc-module-cup-aw-leibniz).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules

open scoped BigOperators
noncomputable section

private theorem front_left (p q n : ℕ) (h : p + q = n) (i : Fin (p + 1)) :
    SimplexCategory.subinterval (n := n) 0 p (by omega) ≫
        SimplexCategory.δ ⟨i, by omega⟩ =
      SimplexCategory.δ i.castSucc ≫
        SimplexCategory.subinterval (n := n + 1) 0 (p + 1) (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove ⟨i.val, _⟩ ⟨k.val + 0, _⟩).val =
    (Fin.succAbove i.castSucc k).val + 0
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

private theorem back_left (p q n : ℕ) (h : p + q = n) (i : Fin (p + 1)) :
    SimplexCategory.subinterval (n := n) p q (by omega) ≫
        SimplexCategory.δ ⟨i, by omega⟩ =
      SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove ⟨i.val, _⟩ ⟨k.val + p, _⟩).val = k.val + (p + 1)
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · change i.val ≤ k.val + p
    omega

private theorem front_right (p q n : ℕ) (h : p + q = n) (j : Fin (q + 1)) :
    SimplexCategory.subinterval (n := n) 0 p (by omega) ≫
        SimplexCategory.δ ⟨p + j.val + 1, by omega⟩ =
      SimplexCategory.subinterval (n := n + 1) 0 p (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove ⟨p + j.val + 1, _⟩ ⟨k.val + 0, _⟩).val = k.val + 0
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change k.val + 0 < p + j.val + 1
    omega

private theorem back_right (p q n : ℕ) (h : p + q = n) (j : Fin (q + 1)) :
    SimplexCategory.subinterval (n := n) p q (by omega) ≫
        SimplexCategory.δ ⟨p + j.val + 1, by omega⟩ =
      SimplexCategory.δ j.succ ≫
        SimplexCategory.subinterval (n := n + 1) p (q + 1) (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove ⟨p + j.val + 1, _⟩ ⟨k.val + p, _⟩).val =
    (Fin.succAbove j.succ k).val + p
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

private theorem front_middle (p q n : ℕ) (h : p + q = n) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫
        SimplexCategory.subinterval (n := n + 1) 0 (p + 1) (by omega) =
      SimplexCategory.subinterval (n := n + 1) 0 p (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove (Fin.last (p + 1)) k).val + 0 = k.val + 0
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact Fin.castSucc_lt_last k

private theorem back_middle (p q n : ℕ) (h : p + q = n) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫
        SimplexCategory.subinterval (n := n + 1) p (q + 1) (by omega) =
      SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega) := by
  ext k : 3
  have hk : k.val < _ := k.isLt
  dsimp only [SimplexCategory.len_mk] at hk
  simp only [SimplexCategory.subinterval, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  change (Fin.succAbove (0 : Fin (q + 2)) k).val + p = k.val + (p + 1)
  rw [Fin.succAbove_of_le_castSucc]
  · simp only [Fin.val_succ]
    omega
  · exact Fin.zero_le _

private def raw (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : SimplexCategory ⥤ X.Modules) (μ : ∀ m : ℕ, A.obj ⦋m⦌ ⊗ B.obj ⦋m⦌ ⟶ C.obj ⦋m⦌)
    (p q n : ℕ) (h : p + q = n) : A.obj ⦋p⦌ ⊗ B.obj ⦋q⦌ ⟶ C.obj ⦋n⦌ :=
  (A.map (SimplexCategory.subinterval (n := n) 0 p (by omega)) ⊗ₘ
    B.map (SimplexCategory.subinterval (n := n) p q (by omega))) ≫ μ n

private theorem raw_coface (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : SimplexCategory ⥤ X.Modules) (μ : ∀ m : ℕ, A.obj ⦋m⦌ ⊗ B.obj ⦋m⦌ ⟶ C.obj ⦋m⦌)
    (hμ : ∀ (m : ℕ) (i : Fin (m + 2)),
      (A.map (SimplexCategory.δ i) ⊗ₘ B.map (SimplexCategory.δ i)) ≫ μ (m + 1) =
        μ m ≫ C.map (SimplexCategory.δ i))
    (p q n : ℕ) (h : p + q = n) (i : Fin (n + 2)) :
    raw X A B C μ p q n h ≫ C.map (SimplexCategory.δ i) =
      (A.map (SimplexCategory.subinterval (n := n) 0 p (by omega) ≫
          SimplexCategory.δ i) ⊗ₘ
        B.map (SimplexCategory.subinterval (n := n) p q (by omega) ≫
          SimplexCategory.δ i)) ≫ μ (n + 1) := by
  unfold raw
  rw [Category.assoc, ← hμ n i]
  erw [tensorHom_comp_tensorHom_assoc]
  rw [← A.map_comp, ← B.map_comp]


private theorem raw_left (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : SimplexCategory ⥤ X.Modules) (μ : ∀ m : ℕ, A.obj ⦋m⦌ ⊗ B.obj ⦋m⦌ ⟶ C.obj ⦋m⦌)
    (p q n : ℕ) (h : p + q = n) (i : Fin (p + 2)) :
    A.map (SimplexCategory.δ i) ▷ B.obj ⦋q⦌ ≫
        raw X A B C μ (p + 1) q (n + 1) (by omega) =
      (A.map (SimplexCategory.δ i ≫
          SimplexCategory.subinterval (n := n + 1) 0 (p + 1) (by omega)) ⊗ₘ
        B.map (SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega))) ≫
        μ (n + 1) := by
  unfold raw
  erw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
  rw [Category.id_comp, ← A.map_comp]

private theorem raw_right (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : SimplexCategory ⥤ X.Modules) (μ : ∀ m : ℕ, A.obj ⦋m⦌ ⊗ B.obj ⦋m⦌ ⟶ C.obj ⦋m⦌)
    (p q n : ℕ) (h : p + q = n) (j : Fin (q + 2)) :
    A.obj ⦋p⦌ ◁ B.map (SimplexCategory.δ j) ≫
        raw X A B C μ p (q + 1) (n + 1) (by omega) =
      (A.map (SimplexCategory.subinterval (n := n + 1) 0 p (by omega)) ⊗ₘ
        B.map (SimplexCategory.δ j ≫
          SimplexCategory.subinterval (n := n + 1) p (q + 1) (by omega))) ≫
        μ (n + 1) := by
  unfold raw
  erw [← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  rw [Category.id_comp, ← B.map_comp]

private theorem split_sum {M : Type*} [AddCommMonoid M] (p q n : ℕ) (h : p + q = n)
    (f : Fin (n + 2) → M) :
    (∑ i, f i) =
      (∑ i : Fin (p + 1), f ⟨i.val, by omega⟩) +
      ∑ j : Fin (q + 1), f ⟨p + j.val + 1, by omega⟩ := by
  let e : Fin (p + 1 + (q + 1)) ≃ Fin (n + 2) :=
    finCongr (by omega)
  rw [← Fintype.sum_equiv e (fun i ↦ f (e i)) f (fun i ↦ rfl), Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Fin.ext
    change p + 1 + j.val = p + j.val + 1
    omega


private theorem raw_leibniz (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : SimplexCategory ⥤ X.Modules) (μ : ∀ m : ℕ, A.obj ⦋m⦌ ⊗ B.obj ⦋m⦌ ⟶ C.obj ⦋m⦌)
    (hμ : ∀ (m : ℕ) (i : Fin (m + 2)),
      (A.map (SimplexCategory.δ i) ⊗ₘ B.map (SimplexCategory.δ i)) ≫ μ (m + 1) =
        μ m ≫ C.map (SimplexCategory.δ i))
    (p q n : ℕ) (h : p + q = n) :
    raw X A B C μ p q n h ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • C.map (SimplexCategory.δ i)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • A.map (SimplexCategory.δ i)) ▷ B.obj ⦋q⦌ ≫
        raw X A B C μ (p + 1) q (n + 1) (by omega) +
      (-1 : ℤ) ^ p • (A.obj ⦋p⦌ ◁
        (∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val • B.map (SimplexCategory.δ i)) ≫
        raw X A B C μ p (q + 1) (n + 1) (by omega)) := by
  simp -implicitDefEqProofs only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    sum_whiskerRight, whiskerLeft_sum,
    zsmul_whiskerRight, whiskerLeft_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp]
  simp_rw (config := { implicitDefEqProofs := false }) [raw_coface X A B C μ hμ p q n h,
    raw_left X A B C μ p q n h, raw_right X A B C μ p q n h]
  let T (i : Fin (n + 2)) := (-1 : ℤ) ^ i.val •
    ((A.map (SimplexCategory.subinterval (n := n) 0 p (by omega) ≫
        SimplexCategory.δ i) ⊗ₘ
      B.map (SimplexCategory.subinterval (n := n) p q (by omega) ≫
        SimplexCategory.δ i)) ≫ μ (n + 1))
  let L (i : Fin (p + 2)) := (-1 : ℤ) ^ i.val •
    ((A.map (SimplexCategory.δ i ≫
        SimplexCategory.subinterval (n := n + 1) 0 (p + 1) (by omega)) ⊗ₘ
      B.map (SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega))) ≫
      μ (n + 1))
  let R (j : Fin (q + 2)) := (-1 : ℤ) ^ j.val •
    ((A.map (SimplexCategory.subinterval (n := n + 1) 0 p (by omega)) ⊗ₘ
      B.map (SimplexCategory.δ j ≫
        SimplexCategory.subinterval (n := n + 1) p (q + 1) (by omega))) ≫
      μ (n + 1))
  change (∑ i, T i) = (∑ i, L i) + (-1 : ℤ) ^ p • ∑ j, R j
  rw [split_sum p q n h, Fin.sum_univ_castSucc L, Fin.sum_univ_succ R,
    smul_add, Finset.smul_sum]
  dsimp only [T, L, R, Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ]
  simp_rw (config := { implicitDefEqProofs := false })
    [front_left p q n h, back_left p q n h, front_right p q n h,
      back_right p q n h, front_middle p q n h, back_middle p q n h]
  simp only [pow_zero, one_smul, pow_add, pow_succ, mul_neg,
    mul_one, neg_smul]
  simp only [smul_neg, ← mul_zsmul]
  abel


private def naturalIso (X : Scheme.{u}) (A : CosimplicialObject X.Modules) (n : ℕ) :
    (moduleCup_cosimplicialComplex X A).X (n : ℤ) ≅ A.obj ⦋n⦌ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl

private theorem aw_nat (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (p q n : ℕ) (h : p + q = n) :
    moduleCup_awSummand X A B C μ (p : ℤ) (q : ℤ) (n : ℤ) (by exact_mod_cast h) =
      ((naturalIso X A p).hom ⊗ₘ (naturalIso X B q).hom) ≫
        raw X A B C (fun m ↦ μ.app ⦋m⦌) p q n h ≫ (naturalIso X C n).inv := by
  subst n
  simp only [moduleCup_awSummand, Int.natCast_nonneg, ↓reduceDIte, Int.toNat_natCast]
  rfl

private theorem d_nat (X : Scheme.{u}) (A : CosimplicialObject X.Modules) (p : ℕ) :
    (moduleCup_cosimplicialComplex X A).d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
      (naturalIso X A p).hom ≫ AlternatingCofaceMapComplex.objD A p ≫
        (naturalIso X A (p + 1)).inv := by
  have hd := HomologicalComplex.extend_d_eq
    ((alternatingCofaceMapComplex X.Modules).obj A) ComplexShape.embeddingUpNat
      (i := p) (j := p + 1) rfl rfl
  change _ = _ ≫ ((alternatingCofaceMapComplex X.Modules).obj A).d p (p + 1) ≫ _ at hd
  simpa only [ComplexShape.embeddingUpNat, ComplexShape.Embedding.mk',
    moduleCup_cosimplicialComplex, naturalIso,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlternatingCofaceMapComplex.obj, CochainComplex.of_d] using hd


private theorem transport_pairing
    {D : Type*} [Category D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    {A₀ A₁ B₀ B₁ C₀ C₁ a₀ a₁ b₀ b₁ c₀ c₁ : D}
    (eA₀ : A₀ ≅ a₀) (eA₁ : A₁ ≅ a₁) (eB₀ : B₀ ≅ b₀) (eB₁ : B₁ ≅ b₁)
    (eC₀ : C₀ ≅ c₀) (eC₁ : C₁ ≅ c₁)
    (da : a₀ ⟶ a₁) (db : b₀ ⟶ b₁) (dc : c₀ ⟶ c₁)
    (t : a₀ ⊗ b₀ ⟶ c₀) (tl : a₁ ⊗ b₀ ⟶ c₁) (tr : a₀ ⊗ b₁ ⟶ c₁) (z : ℤ)
    (h : t ≫ dc = da ▷ b₀ ≫ tl + z • (a₀ ◁ db ≫ tr)) :
    ((eA₀.hom ⊗ₘ eB₀.hom) ≫ t ≫ eC₀.inv) ≫ (eC₀.hom ≫ dc ≫ eC₁.inv) =
      (eA₀.hom ≫ da ≫ eA₁.inv) ▷ B₀ ≫
          ((eA₁.hom ⊗ₘ eB₀.hom) ≫ tl ≫ eC₁.inv) +
        z • (A₀ ◁ (eB₀.hom ≫ db ≫ eB₁.inv) ≫
          ((eA₀.hom ⊗ₘ eB₁.hom) ≫ tr ≫ eC₁.inv)) := by
  have hl : (eA₀.hom ⊗ₘ eB₀.hom) ≫ da ▷ b₀ =
      (eA₀.hom ≫ da ≫ eA₁.inv) ▷ B₀ ≫ (eA₁.hom ⊗ₘ eB₀.hom) := by
    simp only [tensorHom_comp_whiskerRight, whiskerRight_comp_tensorHom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hr : (eA₀.hom ⊗ₘ eB₀.hom) ≫ a₀ ◁ db =
      A₀ ◁ (eB₀.hom ≫ db ≫ eB₁.inv) ≫ (eA₀.hom ⊗ₘ eB₁.hom) := by
    simp only [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = ((eA₀.hom ⊗ₘ eB₀.hom) ≫ (t ≫ dc)) ≫ eC₁.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = ((eA₀.hom ⊗ₘ eB₀.hom) ≫
        (da ▷ b₀ ≫ tl + z • (a₀ ◁ db ≫ tr))) ≫ eC₁.inv := by rw [h]
    _ = _ := by
      simp only [Preadditive.comp_add, Preadditive.add_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      rw [← Category.assoc (eA₀.hom ⊗ₘ eB₀.hom) (da ▷ b₀), hl,
        ← Category.assoc (eA₀.hom ⊗ₘ eB₀.hom) (a₀ ◁ db), hr]
      simp only [Category.assoc]

/-- The signed differential calculation on a single nonnegative bidegree.
Source: Banerjee, Tensor Structure on Smooth Motives, arXiv:1004.1491,
§1.1.4, p. 16, the front/back formula immediately before (1.1.2).
(blueprint: lem-sc-module-cup-aw-leibniz)

Proof: Write f_{r,s}(i)=i and b_{r,s}(j)=r+j for the front and back inclusions.
Transport the differentials along the three extension isomorphisms, so they
are the alternating sums of cofaces. Naturality of μ rewrites a target coface
as the simultaneous coface on the two factors before μ. For a coface indexed
by i ≤ r, its composites with f_{r,s} and b_{r,s} are respectively
f_{r+1,s} after the i-th coface and b_{r+1,s}. These give the first r+1
terms of the differential of A. For i > r, the composites are f_{r,s+1}
and b_{r,s+1} after the (i-r)-th coface; these are the last s+1 terms
of (-1)^r times the differential of B. The missing term of the first sum
(index r+1) and the missing term of the second sum (index 0) have the same
pair of simplex maps and opposite signs, hence cancel. Additivity of tensor
and composition transports these finite-sum identities to sheaf morphisms.
Conjugating back gives the displayed equality, with the standard total sign.
At r=s=0 the four terms before μ in degree one are Aδ⁰ tensor Bδ⁰,
minus Aδ¹ tensor Bδ⁰, plus Aδ¹ tensor Bδ⁰, minus Aδ¹ tensor Bδ¹.
The middle terms cancel, and naturality identifies the others with the two
target cofaces after μ in degree zero. No degeneration, exactness or nonzero
object assumption is used, so zero sheaves and the empty scheme also satisfy it. -/
theorem moduleCup_awSummand_leibniz (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (r s n : ℤ) (h : r + s = n) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    moduleCup_awSummand X A B C μ r s n h ≫
        (moduleCup_cosimplicialComplex X C).d n (n + 1) =
      (moduleCup_cosimplicialComplex X A).d r (r + 1) ▷
          (moduleCup_cosimplicialComplex X B).X s ≫
        moduleCup_awSummand X A B C μ (r + 1) s (n + 1) (by omega) +
      r.negOnePow • ((moduleCup_cosimplicialComplex X A).X r ◁
          (moduleCup_cosimplicialComplex X B).d s (s + 1) ≫
        moduleCup_awSummand X A B C μ r (s + 1) (n + 1) (by omega)) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = r := ⟨r.toNat, Int.toNat_of_nonneg hr⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = s := ⟨s.toNat, Int.toNat_of_nonneg hs⟩
  obtain rfl : n = ((p + q : ℕ) : ℤ) := by omega
  change moduleCup_awSummand X A B C μ (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) _ ≫
      (moduleCup_cosimplicialComplex X C).d ((p + q : ℕ) : ℤ)
        ((p + q + 1 : ℕ) : ℤ) =
    (moduleCup_cosimplicialComplex X A).d (p : ℤ) ((p + 1 : ℕ) : ℤ) ▷
        (moduleCup_cosimplicialComplex X B).X (q : ℤ) ≫
      moduleCup_awSummand X A B C μ ((p + 1 : ℕ) : ℤ) (q : ℤ)
        ((p + q + 1 : ℕ) : ℤ) _ +
    (p : ℤ).negOnePow • ((moduleCup_cosimplicialComplex X A).X (p : ℤ) ◁
        (moduleCup_cosimplicialComplex X B).d (q : ℤ) ((q + 1 : ℕ) : ℤ) ≫
      moduleCup_awSummand X A B C μ (p : ℤ) ((q + 1 : ℕ) : ℤ)
        ((p + q + 1 : ℕ) : ℤ) _)
  rw [aw_nat X A B C μ p q (p + q) rfl,
    aw_nat X A B C μ (p + 1) q (p + q + 1) (by omega),
    aw_nat X A B C μ p (q + 1) (p + q + 1) (by omega),
    d_nat X A p, d_nat X B q, d_nat X C (p + q)]
  simp only [Units.smul_def, Int.coe_negOnePow_natCast]
  apply transport_pairing
  have hm : ∀ (m : ℕ) (i : Fin (m + 2)),
      (A.map (SimplexCategory.δ i) ⊗ₘ B.map (SimplexCategory.δ i)) ≫ μ.app ⦋m + 1⦌ =
        μ.app ⦋m⦌ ≫ C.map (SimplexCategory.δ i) := by
    intro m i
    exact μ.naturality (SimplexCategory.δ i)
  simpa only [AlternatingCofaceMapComplex.objD, CosimplicialObject.δ] using
    raw_leibniz X A B C (fun m ↦ μ.app ⦋m⦌) hm p q (p + q) rfl


end
end AlgebraicGeometry.Scheme.Modules
