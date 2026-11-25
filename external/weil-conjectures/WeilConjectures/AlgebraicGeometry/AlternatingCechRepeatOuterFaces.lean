/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The outer faces of a duplicated first repeat

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
(blueprint: lem-pc-alternating-cech-repeat-outer-faces)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem mapped_sections_eq (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t₁ t₂ : Fin (p + 1) → I) (h : t₁ = t₂)
    (Z : X.Opens) (f : Z ⟶ S.W p t₁) (g : Z ⟶ S.W p t₂) :
    F.map f.op (s t₁) = F.map g.op (s t₂) := by
  subst t₂
  rw [show f = g from Subsingleton.elim _ _]

private theorem adjacent_faces_eq {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 2) → I) (a : Fin (p + 2)) (ha : cechFirstRepeat t a) :
    t ∘ a.succAbove = t ∘ (⟨a.val + 1, ha.choose⟩ : Fin (p + 2)).succAbove := by
  obtain ⟨ha', he, _⟩ := ha
  funext k
  simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> try rfl
  all_goals
    have hk : k.val = a.val := by omega
    have h₁ : k.castSucc = a := by ext; exact hk
    have h₂ : k.succ = (⟨a.val + 1, ha'⟩ : Fin (p + 2)) := by ext; simpa using hk
    rw [h₁, h₂]
    first | exact he | exact he.symm

private theorem face_val {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

private theorem firstRepeat_face {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 2) → I) (ht : Monotone t)
    (a : Fin (p + 2)) (ha : cechFirstRepeat t a)
    (j : Fin (p + 2)) (hj : j.val < a.val ∨ a.val + 1 < j.val)
    (b : Fin (p + 1))
    (hb : b.val = if j.val < a.val then a.val - 1 else a.val) :
    cechFirstRepeat (t ∘ j.succAbove) b := by
  obtain ⟨ha', he, hprefix⟩ := ha
  have hb' : b.val + 1 < p + 1 := by
    split_ifs at hb <;> omega
  refine ⟨hb', ?_, ?_⟩
  · have h₁ : j.succAbove b = a := by
      apply Fin.ext
      rw [face_val]
      split_ifs at * <;> omega
    have h₂ : j.succAbove (⟨b.val + 1, hb'⟩ : Fin (p + 1)) =
        (⟨a.val + 1, ha'⟩ : Fin (p + 2)) := by
      apply Fin.ext
      rw [face_val]
      try dsimp only [Fin.val_mk]
      split_ifs at * <;> omega
    simpa only [Function.comp_apply, h₁, h₂] using he
  · intro k hk
    have hka : (j.succAbove k).val < a.val := by
      rw [face_val]
      split_ifs at * <;> omega
    have hle : (⟨(j.succAbove k).val + 1, by omega⟩ : Fin (p + 2)) ≤
        j.succAbove (⟨k.val + 1, by omega⟩ : Fin (p + 1)) := by
      change (j.succAbove k).val + 1 ≤ _
      rw [face_val, face_val]
      try dsimp only [Fin.val_mk]
      split_ifs <;> omega
    exact lt_of_lt_of_le (hprefix (j.succAbove k) hka) (ht hle)

private theorem junction_val {p : ℕ} (a : Fin (p + 1)) (k : Fin (p + 2)) :
    (cechJunction (Equiv.refl _) (Equiv.refl _) a k).val =
      if k.val ≤ a.val then k.val else k.val - 1 := by
  simp only [cechJunction]
  split_ifs <;> rfl

private theorem outer_index_pair {p : ℕ}
    (a : Fin (p + 2)) (j : Fin (p + 2))
    (hj : j.val < a.val ∨ a.val + 1 < j.val)
    (b : Fin (p + 1))
    (hb : b.val = if j.val < a.val then a.val - 1 else a.val) :
    cechJunction (Equiv.refl _) (Equiv.refl _) a ∘
        (a.succ.succAbove j).succAbove =
      j.succAbove ∘ cechJunction (Equiv.refl _) (Equiv.refl _) b := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, junction_val, face_val, Fin.val_succ]
  split_ifs at * <;> omega

private theorem outer_term_pair (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) (ht : Monotone t)
    (a : Fin (p + 2)) (ha : cechFirstRepeat t a)
    (j : Fin (p + 2)) (hj : j.val < a.val ∨ a.val + 1 < j.val) :
    let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
    let r := a.succ.succAbove j
    ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ r.val) •
        F.map (S.indexMap t q).op
          (F.map (S.indexMap (t ∘ q) r.succAbove).op
            (s ((t ∘ q) ∘ r.succAbove))) =
      -((-1 : ℤ) ^ j.val • F.map (S.indexMap t j.succAbove).op
        ((cechSecondSortingHom X U F S p) s (t ∘ j.succAbove))) := by
  classical
  dsimp only
  let b : Fin (p + 1) := ⟨if j.val < a.val then a.val - 1 else a.val, by
    obtain ⟨ha', _, _⟩ := ha
    split_ifs <;> omega⟩
  have hb : b.val = if j.val < a.val then a.val - 1 else a.val := rfl
  have hstable {J : Type v} [LinearOrder J] {n : ℕ}
      (u : Fin n → J) (hu : Monotone u) (σ : Equiv.Perm (Fin n))
      (hσ : cechStableSort u σ) : σ = Equiv.refl _ := by
    apply (Equiv.Perm.monotone_iff σ).mp
    apply StrictMono.monotone
    intro i k hik
    by_contra h
    have hle : σ k ≤ σ i := le_of_not_gt h
    have he : u (σ i) = u (σ k) :=
      le_antisymm (hσ.1 (le_of_lt hik)) (hu hle)
    exact (not_lt_of_ge hle) (hσ.2 i k hik he)
  have hfirst {J : Type v} [LinearOrder J] {n : ℕ}
      (u : Fin (n + 1) → J) (x y : Fin (n + 1))
      (hx : cechFirstRepeat u x) (hy : cechFirstRepeat u y) : x = y := by
    obtain ⟨hx', hxe, hxp⟩ := hx
    obtain ⟨hy', hye, hyp⟩ := hy
    apply le_antisymm
    · by_contra h
      have hyx : y.val < x.val := by omega
      exact (ne_of_lt (hxp y hyx)) hye
    · by_contra h
      have hxy : x.val < y.val := by omega
      exact (ne_of_lt (hyp x hxy)) hxe
  have hsecond : (cechSecondSortingHom X U F S p) s (t ∘ j.succAbove) =
      (-1 : ℤ) ^ b.val • F.map
        (S.indexMap (t ∘ j.succAbove)
          (cechJunction (Equiv.refl _) (Equiv.refl _) b)).op
        (s ((t ∘ j.succAbove) ∘
          cechJunction (Equiv.refl _) (Equiv.refl _) b)) := by
    classical
    change (∑ σ : Equiv.Perm (Fin (p + 1)), ∑ c : Fin (p + 1),
      if cechStableSort (t ∘ j.succAbove) σ ∧
          cechFirstRepeat ((t ∘ j.succAbove) ∘ σ) c then
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ c.val) •
          F.map (S.indexMap (t ∘ j.succAbove)
            (cechJunction σ σ c)).op
            (s ((t ∘ j.succAbove) ∘ cechJunction σ σ c)) else 0) = _
    rw [Finset.sum_eq_single (Equiv.refl _)]
    · rw [Finset.sum_eq_single b]
      · have hs : cechStableSort (t ∘ j.succAbove) (Equiv.refl _) :=
          ⟨(ht.comp (Fin.strictMono_succAbove j).monotone),
            fun _ _ h _ ↦ h⟩
        simp [hs, firstRepeat_face t ht a ha j hj b hb]
      · intro c _ hcb
        have hc : ¬ cechFirstRepeat (t ∘ j.succAbove) c := fun hc ↦
          hcb (hfirst (t ∘ j.succAbove) c b hc
            (firstRepeat_face t ht a ha j hj b hb))
        simp [hc]
      · simp
    · intro σ _ hσ
      have hn : ¬ cechStableSort (t ∘ j.succAbove) σ := fun hs ↦
        hσ (hstable (t ∘ j.succAbove)
          (ht.comp (Fin.strictMono_succAbove j).monotone) σ hs)
      simp [hn]
    · simp
  rw [hsecond]
  rw [map_zsmul, smul_smul]
  have he : (t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a) ∘
        (a.succ.succAbove j).succAbove =
      (t ∘ j.succAbove) ∘ cechJunction (Equiv.refl _) (Equiv.refl _) b := by
    funext k
    exact congrArg t (congrFun (outer_index_pair a j hj b hb) k)
  have hm := mapped_sections_eq X U F S (p + 1) s _ _ he (S.W (p + 1) t)
    (S.indexMap t (cechJunction (Equiv.refl _) (Equiv.refl _) a) ≫
      S.indexMap (t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a)
        (a.succ.succAbove j).succAbove)
    (S.indexMap t j.succAbove ≫
      S.indexMap (t ∘ j.succAbove) (cechJunction (Equiv.refl _) (Equiv.refl _) b))
  simp only [op_comp, F.map_comp, AddCommGrpCat.comp_apply] at hm
  rw [hm, ← neg_smul]
  congr 1
  by_cases hja : j.val < a.val
  · have hr : (a.succ.succAbove j).val = j.val := by
      rw [face_val]; simp only [Fin.val_succ]; rw [ite_eq_left (by omega)]
    have hab : a.val = b.val + 1 := by rw [hb, ite_eq_left hja]; omega
    rw [hr, hab, pow_succ]
    ring
  · have hr : (a.succ.succAbove j).val = j.val + 1 := by
      rw [face_val]; simp only [Fin.val_succ]; rw [ite_eq_right (by omega)]
    rw [hr, hb, ite_eq_right hja, pow_succ]
    ring

/-- The faces outside the tripled value cancel the incoming homotopy boundary.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2
and the verification omitted immediately after it.
Proof: Write q for duplication at a. For each deletion j<a from the duplicated tuple,
pair its term with deletion j from t followed by duplication at a-1. For each
j>a+2, pair with deletion j-1 from t followed by duplication at a. The resulting
tuples agree and their restriction composites agree, since Opens is a thin
category. The sign products differ by a factor -1. In the incoming differential,
the terms deleting a and a+1 have the same tuple and equal restrictions and
opposite signs, so cancel, regardless of where that face's first repeat lies.
Every other incoming term is one of the paired terms just described. Distribute
the finite sums and cancel these pairs.
(blueprint: lem-pc-alternating-cech-repeat-outer-faces) -/
theorem cechRepeatOuterFaces (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) (hp : 0 < p)
    (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) (ht : Monotone t)
    (a : Fin (p + 2)) (ha : cechFirstRepeat t a) :
    let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
    (∑ j : Fin (p + 3), if j.val < a.val ∨ a.val + 2 < j.val then
      ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) •
        F.map (S.indexMap t q).op
          (F.map (S.indexMap (t ∘ q) j.succAbove).op
            (s ((t ∘ q) ∘ j.succAbove))) else 0) = 
      -S.differentialValue F p ((cechSecondSortingHom X U F S p) s) t := by
  classical
  have _ := hp
  dsimp only
  let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
  let K := (cechSecondSortingHom X U F S p) s
  let D (j : Fin (p + 2)) := (-1 : ℤ) ^ j.val •
    F.map (S.indexMap t j.succAbove).op (K (t ∘ j.succAbove))
  let O (r : Fin (p + 3)) := if r.val < a.val ∨ a.val + 2 < r.val then
    ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ r.val) •
      F.map (S.indexMap t q).op
        (F.map (S.indexMap (t ∘ q) r.succAbove).op
          (s ((t ∘ q) ∘ r.succAbove))) else 0
  let P (j : Fin (p + 2)) := j.val < a.val ∨ a.val + 1 < j.val
  change (∑ r, O r) = -(∑ j, D j)
  have hO : O a.succ = 0 := by
    dsimp only [O, Fin.val_succ]
    rw [ite_eq_right (by omega)]
  have hpair (j : Fin (p + 2)) :
      O (a.succ.succAbove j) = if P j then -D j else 0 := by
    have hP : ((a.succ.succAbove j).val < a.val ∨
        a.val + 2 < (a.succ.succAbove j).val) ↔ P j := by
      dsimp only [P]
      rw [face_val]
      simp only [Fin.val_succ]
      split_ifs <;> omega
    dsimp only [O]
    by_cases hj : P j
    · rw [ite_eq_left (hP.mpr hj), ite_eq_left hj]
      exact outer_term_pair X U F S p s t ht a ha j hj
    · rw [ite_eq_right (fun h ↦ hj (hP.mp h)), ite_eq_right hj]
  let a₁ : Fin (p + 2) := ⟨a.val + 1, ha.choose⟩
  have hmaps := mapped_sections_eq X U F S p K _ _ (adjacent_faces_eq t a ha)
    (S.W (p + 1) t) (S.indexMap t a.succAbove) (S.indexMap t a₁.succAbove)
  have hcentral : D a + D a₁ = 0 := by
    dsimp only [D]
    rw [hmaps]
    dsimp only [a₁, Fin.val_mk]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, add_neg_cancel]
  have hset : Finset.univ.filter (fun j ↦ ¬ P j) = {a, a₁} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    dsimp only [P]
    constructor
    · intro hj
      have hv : j.val = a.val ∨ j.val = a.val + 1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    · rintro (rfl | rfl) <;> (try dsimp only [a₁, Fin.val_mk]) <;> omega
  have hne : a ≠ a₁ := by
    intro h
    have hval := congrArg Fin.val h
    dsimp only [a₁, Fin.val_mk] at hval
    omega
  have hzero : (∑ j : Fin (p + 2), if ¬ P j then D j else 0) = 0 := by
    rw [← Finset.sum_filter, hset]
    simpa only [Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true,
      Finset.sum_singleton] using hcentral
  have hsum : (∑ j : Fin (p + 2), D j) =
      ∑ j : Fin (p + 2), if P j then D j else 0 := by
    calc
      (∑ j, D j) = (∑ j, if P j then D j else 0) +
          (∑ j, if ¬ P j then D j else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : P j <;> simp only [hj, not_true_eq_false, not_false_eq_true,
          ite_true, ite_false, zero_add, add_zero]
      _ = _ := by rw [hzero, add_zero]
  rw [Fin.sum_univ_succAbove O a.succ, hO, zero_add, hsum]
  calc
    (∑ j, O (a.succ.succAbove j)) = ∑ j, -(if P j then D j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hpair]
      by_cases hj : P j <;> simp [hj]
    _ = _ := Finset.sum_neg_distrib _

end AlgebraicGeometry.Scheme
