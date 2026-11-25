/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The two duplicate faces cancel by the alternating permutation law.
Proof: construct the permutation exchanging the equal entries, apply the alternating
cochain law, compare restriction composites by the fibre-product universal property,
and use the opposite face signs to cancel.
(blueprint: lem-pc-cech-differential-repeated-cancellation) -/
theorem cechDifferential_repeated_cancellation (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p) (t : Fin (p + 2) → I)
    (a b : Fin (p + 2)) (hab : a ≠ b) (htab : t a = t b)
    (hc : ∀ (s : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c s = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap s σ).op (c (s ∘ σ))) :
    (∑ j : ({a, b} : Finset (Fin (p + 2))),
      (-1 : ℤ) ^ (j : Fin (p + 2)).val •
        (F.map (S.indexMap t (j : Fin (p + 2)).succAbove).op)
          (c (t ∘ (j : Fin (p + 2)).succAbove))) = 0 := by
  classical
  let f : Fin (p + 2) → F.obj (Opposite.op (S.W (p + 1) t)) :=
    fun j ↦ (-1 : ℤ) ^ j.val •
      (F.map (S.indexMap t j.succAbove).op) (c (t ∘ j.succAbove))
  have hpair (a b : Fin (p + 2)) (hab : a < b) (htab : t a = t b) :
      f a + f b = 0 := by
    -- Rotating positions a through b-1 matches the two tuples after deletion.
    let i : Fin (p + 1) := ⟨a.val, by omega⟩
    let j : Fin (p + 1) := ⟨b.val - 1, by omega⟩
    let σ := Fin.cycleIcc i j
    have hij : i ≤ j := by simp only [i, j, Fin.le_def]; omega
    have he : (t ∘ b.succAbove) ∘ σ = t ∘ a.succAbove := by
      funext k
      dsimp only [Function.comp_apply]
      by_cases hk₁ : k < i
      · rw [show σ k = k from Fin.cycleIcc_of_lt hk₁]
        congr 1
        rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
        all_goals simp only [i, j, Fin.lt_def, Fin.le_def, Fin.val_castSucc] at *; omega
      · by_cases hk₂ : j < k
        · rw [show σ k = k from Fin.cycleIcc_of_gt hk₂]
          congr 1
          rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
          all_goals simp only [i, j, Fin.lt_def, Fin.le_def, Fin.val_castSucc] at *; omega
        · by_cases hk₃ : k = j
          · subst k
            rw [show σ j = i from Fin.cycleIcc_of_last hij]
            have hbi : b.succAbove i = a := by
              rw [Fin.succAbove_of_castSucc_lt]
              · apply Fin.ext; rfl
              · simp only [i, Fin.lt_def, Fin.val_castSucc]; omega
            have haj : a.succAbove j = b := by
              rw [Fin.succAbove_of_le_castSucc]
              · apply Fin.ext; dsimp [j]; omega
              · simp only [i, j, Fin.lt_def, Fin.le_def, Fin.val_castSucc] at *; omega
            rw [hbi, haj, htab]
          · have hki : i ≤ k := le_of_not_gt hk₁
            have hkj : k < j := lt_of_le_of_ne (le_of_not_gt hk₂) hk₃
            have hkval : k.val < b.val - 1 := hkj
            have hkbound : k.val + 1 < p + 1 := by omega
            have hv : (k + 1).val = k.val + 1 :=
              Fin.val_add_one_of_lt' hkbound
            rw [show σ k = k + 1 from Fin.cycleIcc_of_ge_of_lt hki hkj]
            have hb : (k + 1).castSucc < b := by
              simp only [Fin.lt_def, Fin.val_castSucc, hv]
              omega
            have ha : a ≤ k.castSucc := hki
            rw [Fin.succAbove_of_castSucc_lt _ _ hb,
              Fin.succAbove_of_le_castSucc _ _ ha]
            congr 1
            apply Fin.ext
            simpa only [Fin.val_castSucc, Fin.val_succ] using hv
    -- Opens form a thin category, so maps into equal chosen products agree.
    have htransport (s s' : Fin (p + 1) → I) (h : s = s')
        (g : S.W (p + 1) t ⟶ S.W p s) (g' : S.W (p + 1) t ⟶ S.W p s') :
        F.map g.op (c s) = F.map g'.op (c s') := by
      subst s'
      have hg : g = g' := Subsingleton.elim _ _
      rw [hg]
    have hr : F.map (S.indexMap t b.succAbove).op (c (t ∘ b.succAbove)) =
        (Equiv.Perm.sign σ : ℤ) •
          F.map (S.indexMap t a.succAbove).op (c (t ∘ a.succAbove)) := by
      rw [hc (t ∘ b.succAbove) σ, map_zsmul]
      congr 1
      rw [← AddCommGrpCat.comp_apply, ← F.map_comp, ← op_comp]
      exact htransport _ _ he _ _
    -- The cycle sign compensates for the distance between the deleted positions.
    have hs : (-1 : ℤ) ^ b.val * (Equiv.Perm.sign σ : ℤ) =
        -((-1 : ℤ) ^ a.val) := by
      rw [show Equiv.Perm.sign σ = (-1) ^ (j.val - i.val) from
        Fin.sign_cycleIcc_of_le hij]
      simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
      have hpow : (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ (j.val - i.val) =
          -((-1 : ℤ) ^ b.val) := by
        rw [← pow_add]
        have hexp : a.val + (j.val - i.val) + 1 = b.val := by
          simp only [i, j] at *
          omega
        have hp := congrArg (fun n ↦ (-1 : ℤ) ^ n) hexp
        rw [pow_succ] at hp
        linarith
      have hsq : ((-1 : ℤ) ^ (j.val - i.val)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        simp
      calc
        (-1 : ℤ) ^ b.val * (-1 : ℤ) ^ (j.val - i.val) =
            -((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ (j.val - i.val)) *
              (-1 : ℤ) ^ (j.val - i.val) := by rw [hpow]; ring
        _ = -((-1 : ℤ) ^ a.val) := by
          rw [neg_mul, mul_assoc, ← pow_two, hsq, mul_one]
    dsimp [f]
    rw [hr, smul_smul, hs, neg_smul, add_neg_cancel]
  change (∑ j : ({a, b} : Finset (Fin (p + 2))), f j) = 0
  rw [← Finset.sum_subtype ({a, b}) (by simp) f, Finset.sum_pair hab]
  rcases lt_or_gt_of_ne hab with h | h
  · exact hpair a b h htab
  · exact (add_comm (f a) (f b)).trans (hpair b a h htab.symm)

end AlgebraicGeometry.Scheme
