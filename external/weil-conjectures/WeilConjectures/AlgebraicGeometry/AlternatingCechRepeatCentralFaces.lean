/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# The three central faces of a duplicated first repeat

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
(blueprint: lem-pc-alternating-cech-repeat-central-faces)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem transport_section (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t t' : Fin (p + 1) → I) (h : t' = t)
    (f : S.W p t ⟶ S.W p t') : F.map f.op (s t') = s t := by
  subst t'
  have hf : f = 𝟙 _ := Subsingleton.elim _ _
  rw [hf]
  simp

private theorem central_tuple {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 2) → I) (a : Fin (p + 2)) (ha : cechFirstRepeat t a)
    (j : Fin (p + 3)) (hj : a.val ≤ j.val ∧ j.val ≤ a.val + 2) :
    (t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a) ∘ j.succAbove = t := by
  obtain ⟨ha', he, _⟩ := ha
  funext k
  simp only [Function.comp_apply]
  by_cases hkj : k.val < j.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hkj)]
    by_cases hka : k.val ≤ a.val
    · simp only [cechJunction, Fin.val_castSucc, hka, dite_true, Equiv.refl_apply]
    · simp only [cechJunction, Fin.val_castSucc, hka, dite_false, Equiv.refl_apply]
      have hk : k.val = a.val + 1 := by omega
      have h1 : (⟨k.val - 1, by omega⟩ : Fin (p + 2)) = a := by
        apply Fin.ext
        change k.val - 1 = a.val
        omega
      have h2 : k = ⟨a.val + 1, ha'⟩ := by ext; omega
      rw [h1, h2]
      exact he
  · rw [Fin.succAbove_of_le_castSucc _ _ (by exact le_of_not_gt hkj)]
    by_cases hka : k.val + 1 ≤ a.val
    · omega
    · simp only [cechJunction, Fin.val_succ, hka, dite_false, Equiv.refl_apply]
      congr 1

/-- The three deletions in the tripled block have total contribution s(t).

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2
and the verification omitted immediately after it.
Proof: Duplication at the first repeat turns the equal entries at a and a+1 into
three equal entries at a,a+1,a+2. Deleting any of them gives t again. The composite
restriction is the identity after this tuple equality, since Opens is a thin
category. Thus the three transported sections all equal s(t). Their coefficients
are (-1)^a times (-1)^a, (-1)^(a+1), and (-1)^(a+2), respectively. The first
and third are 1 and the middle is -1, so their sum is 1. All other summands
are excluded by the filter.
(blueprint: lem-pc-alternating-cech-repeat-central-faces) -/
theorem cechRepeatCentralFaces (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I)
    (a : Fin (p + 2)) (ha : cechFirstRepeat t a) :
    let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
    (∑ j : Fin (p + 3), if a.val ≤ j.val ∧ j.val ≤ a.val + 2 then
      ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) •
        F.map (S.indexMap t q).op
          (F.map (S.indexMap (t ∘ q) j.succAbove).op
            (s ((t ∘ q) ∘ j.succAbove))) else 0) = s t := by
  classical
  dsimp only
  let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
  have hsection (j : Fin (p + 3)) (hj : a.val ≤ j.val ∧ j.val ≤ a.val + 2) :
      F.map (S.indexMap t q).op
        (F.map (S.indexMap (t ∘ q) j.succAbove).op
          (s ((t ∘ q) ∘ j.succAbove))) = s t := by
    have h := transport_section X U F S (p + 1) s t _ (central_tuple t a ha j hj)
      (S.indexMap t q ≫ S.indexMap (t ∘ q) j.succAbove)
    simpa only [op_comp, F.map_comp, AddCommGrpCat.comp_apply] using h
  have hsum : (∑ j : Fin (p + 3), if a.val ≤ j.val ∧ j.val ≤ a.val + 2 then
      ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) •
        F.map (S.indexMap t q).op
          (F.map (S.indexMap (t ∘ q) j.succAbove).op
            (s ((t ∘ q) ∘ j.succAbove))) else 0) =
      ∑ j : Fin (p + 3), if a.val ≤ j.val ∧ j.val ≤ a.val + 2 then
        ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) • s t else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · rw [hsection j hj]
    · rfl
  rw [hsum]
  obtain ⟨ha', _, _⟩ := ha
  let j₀ : Fin (p + 3) := ⟨a.val, by omega⟩
  let j₁ : Fin (p + 3) := ⟨a.val + 1, by omega⟩
  let j₂ : Fin (p + 3) := ⟨a.val + 2, by omega⟩
  have hfilter : (Finset.univ.filter (fun j : Fin (p + 3) ↦
      a.val ≤ j.val ∧ j.val ≤ a.val + 2)) = {j₀, j₁, j₂} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hj
      have he : j.val = a.val ∨ j.val = a.val + 1 ∨ j.val = a.val + 2 := by omega
      rcases he with he | he | he
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Or.inl (Fin.ext he))
      · exact Or.inr (Or.inr (Fin.ext he))
    · rintro (rfl | rfl | rfl) <;> dsimp [j₀, j₁, j₂] <;> omega
  rw [← Finset.sum_filter, hfilter]
  have h01 : j₀ ≠ j₁ := by
    intro h
    have := congrArg Fin.val h
    dsimp [j₀, j₁] at this
    omega
  have h02 : j₀ ≠ j₂ := by
    intro h
    have := congrArg Fin.val h
    dsimp [j₀, j₂] at this
    omega
  have h12 : j₁ ≠ j₂ := by
    intro h
    have := congrArg Fin.val h
    dsimp [j₁, j₂] at this
    omega
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h01, h02, h12, or_self, not_false_eq_true, Finset.sum_singleton]
  dsimp [j₀, j₁, j₂]
  have hsquare : (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ a.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [pow_succ, hsquare, mul_neg, mul_one, neg_neg,
    one_smul, neg_one_smul]
  abel

end AlgebraicGeometry.Scheme
