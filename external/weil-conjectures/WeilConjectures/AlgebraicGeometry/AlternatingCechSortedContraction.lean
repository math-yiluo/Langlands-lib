/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Data.Fin.Tuple.Sort
import WeilConjectures.AlgebraicGeometry.AlternatingCechRepeatOuterFaces
import WeilConjectures.AlgebraicGeometry.AlternatingCechRepeatCentralFaces

/-!
# AlternatingCechSortedContraction

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-sorted-contraction)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem stableSort_eq_refl {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin n → I) (ht : Monotone t) (σ : Equiv.Perm (Fin n))
    (hσ : cechStableSort t σ) : σ = Equiv.refl _ := by
  apply (Equiv.Perm.monotone_iff σ).mp
  apply StrictMono.monotone
  intro i j hij
  by_contra h
  have hle : σ j ≤ σ i := le_of_not_gt h
  have he : t (σ i) = t (σ j) := le_antisymm (hσ.1 (le_of_lt hij)) (ht hle)
  exact (not_lt_of_ge hle) (hσ.2 i j hij he)

private theorem firstRepeat_unique {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 1) → I) (a b : Fin (p + 1))
    (ha : cechFirstRepeat t a) (hb : cechFirstRepeat t b) : a = b := by
  obtain ⟨ha', hea, hpa⟩ := ha
  obtain ⟨hb', heb, hpb⟩ := hb
  apply le_antisymm
  · by_contra h
    have hba : b.val < a.val := by omega
    exact (ne_of_lt (hpa b hba)) heb
  · by_contra h
    have hab : a.val < b.val := by omega
    exact (ne_of_lt (hpb a hab)) hea

private theorem secondSortingHom_repeat (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F (p + 1)) (t : Fin (p + 1) → I) (ht : Monotone t)
    (a : Fin (p + 1)) (ha : cechFirstRepeat t a) :
    (cechSecondSortingHom X U F S p) s t =
      (-1 : ℤ) ^ a.val • F.map
        (S.indexMap t (cechJunction (Equiv.refl _) (Equiv.refl _) a)).op
        (s (t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a)) := by
  classical
  change (∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
    if cechStableSort t σ ∧ cechFirstRepeat (t ∘ σ) b then
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ b.val) •
        F.map (S.indexMap t (cechJunction σ σ b)).op
          (s (t ∘ cechJunction σ σ b)) else 0) = _
  rw [Finset.sum_eq_single (Equiv.refl _)]
  · rw [Finset.sum_eq_single a]
    · have hs : cechStableSort t (Equiv.refl _) := ⟨ht, fun _ _ h _ ↦ h⟩
      simp [hs, ha]
    · intro b _ hba
      have hb : ¬ cechFirstRepeat t b := fun hb ↦ hba (firstRepeat_unique t b a hb ha)
      simp [hb]
    · simp
  · intro σ _ hσ
    have hn : ¬ cechStableSort t σ := fun hs ↦ hσ (stableSort_eq_refl t ht σ hs)
    simp [hn]
  · simp

private theorem secondSortingHom_strict (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F (p + 1)) (t : Fin (p + 1) → I) (ht : StrictMono t) :
    (cechSecondSortingHom X U F S p) s t = 0 := by
  classical
  change (∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
    if cechStableSort t σ ∧ cechFirstRepeat (t ∘ σ) a then
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ a.val) •
        F.map (S.indexMap t (cechJunction σ σ a)).op
          (s (t ∘ cechJunction σ σ a)) else 0) = 0
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · have he := stableSort_eq_refl t ht.monotone σ h.1
    subst σ
    obtain ⟨ha, hea, _⟩ := h.2
    exact (ne_of_lt (ht (show a < (⟨a.val + 1, ha⟩ : Fin (p + 1)) by
      change a.val < a.val + 1; omega)) hea).elim
  · rfl

private theorem boundary_zero (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) :
    (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f 0 =
      S.differential F 0 ≫ cechSecondSortingHom X U F S 0 := by
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (show
    (ComplexShape.up ℕ).Rel 0 1 from rfl) (by intro l h; change l + 1 = 0 at h; omega)]
  simp [cechSecondSortingFamily, SiteCechComplex.complex, CochainComplex.of.d]

private theorem boundary_succ (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f (p + 1) =
      S.differential F (p + 1) ≫ cechSecondSortingHom X U F S (p + 1) +
        cechSecondSortingHom X U F S p ≫ S.differential F p := by
  rw [Homotopy.nullHomotopicMap'_f (show
    (ComplexShape.up ℕ).Rel p (p + 1) from rfl) (show
    (ComplexShape.up ℕ).Rel (p + 1) (p + 1 + 1) from rfl)]
  simp [cechSecondSortingFamily, SiteCechComplex.complex, CochainComplex.of_d]

private theorem sortedContraction_strict (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t : Fin (p + 1) → I) (ht : StrictMono t) :
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p) s t = 0 := by
  cases p with
  | zero =>
    rw [boundary_zero]
    exact secondSortingHom_strict X U F S 0 _ t ht
  | succ p =>
    rw [boundary_succ]
    change (cechSecondSortingHom X U F S (p + 1)) (S.differential F (p + 1) s) t +
      S.differentialValue F p ((cechSecondSortingHom X U F S p) s) t = 0
    rw [secondSortingHom_strict X U F S (p + 1) _ t ht, zero_add]
    apply Finset.sum_eq_zero
    intro j _
    rw [secondSortingHom_strict X U F S p s _ (ht.comp (Fin.strictMono_succAbove j))]
    simp

private theorem exists_firstRepeat {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 1) → I) (ht : Monotone t) (hn : ¬ StrictMono t) :
    ∃ a, cechFirstRepeat t a := by
  classical
  have hex : ∃ k : ℕ, ∃ hk : k + 1 < p + 1,
      t ⟨k, by omega⟩ = t ⟨k + 1, hk⟩ := by
    have hn' := mt (Fin.strictMono_iff_lt_succ (f := t)).mpr hn
    push Not at hn'
    obtain ⟨i, hi⟩ := hn'
    refine ⟨i.val, by omega, ?_⟩
    exact le_antisymm (ht (by simp)) hi
  obtain ⟨hk, he⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, by omega⟩, hk, he, ?_⟩
  intro b hb
  change b.val < Nat.find hex at hb
  apply lt_of_le_of_ne (ht (show b ≤ ⟨b.val + 1, by omega⟩ by
    change b.val ≤ b.val + 1; omega))
  intro he'
  have hmin := Nat.find_min' hex (show ∃ hk : b.val + 1 < p + 1,
    t ⟨b.val, by omega⟩ = t ⟨b.val + 1, hk⟩ from ⟨by omega, he'⟩)
  omega

/-- The contraction boundary on a nondecreasing tuple.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
Proof: Stable sorting of a nondecreasing tuple is the identity. If the tuple is
strictly increasing, all faces are increasing and the repeated-tuple operator is
zero on the tuple and its faces. Otherwise let a be its first adjacent equality.
Expand the alternating differential and the sum duplicating the first repeat.
Deletions before a pair with face terms having first repeat a-1; deletions after
it pair with face terms having first repeat a. Their signs are opposite. The two
faces deleting the equal occurrences coincide and cancel, even if those faces
are increasing. The three deletions of the tripled value leave the original
tuple, with total coefficient (-1)^a*((-1)^a+(-1)^(a+1)+(-1)^(a+2))=1.
All restriction composites agree by uniqueness of the product map. Thus the
boundary equals the original section on repeated tuples and zero on increasing
tuples. In degree zero there is no repeated tuple and the operator is zero.
(blueprint: lem-pc-alternating-cech-sorted-contraction) -/
theorem cechSortedContraction (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t : Fin (p + 1) → I) (ht : Monotone t) :
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p) s t =
      s t - (if StrictMono t then s t else 0) := by
  classical
  by_cases hs : StrictMono t
  · rw [ite_eq_left hs, sub_self]
    exact sortedContraction_strict X U F S p s t hs
  · rw [ite_eq_right hs, sub_zero]
    obtain ⟨a, ha⟩ := exists_firstRepeat t ht hs
    cases p with
    | zero =>
      obtain ⟨h, _⟩ := ha
      omega
    | succ p =>
      rw [boundary_succ]
      change (cechSecondSortingHom X U F S (p + 1)) (S.differential F (p + 1) s) t +
        S.differentialValue F p ((cechSecondSortingHom X U F S p) s) t = s t
      rw [secondSortingHom_repeat X U F S (p + 1) _ t ht a ha]
      let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
      change (-1 : ℤ) ^ a.val • F.map (S.indexMap t q).op
        (S.differentialValue F (p + 1) s (t ∘ q)) + _ = _
      simp only [SiteCechComplex.differentialValue, map_sum, map_zsmul, Finset.smul_sum,
        smul_smul]
      have hsplit : (∑ j : Fin (p + 3),
          ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) • F.map (S.indexMap t q).op
            (F.map (S.indexMap (t ∘ q) j.succAbove).op
              (s ((t ∘ q) ∘ j.succAbove)))) =
          (∑ j : Fin (p + 3), if j.val < a.val ∨ a.val + 2 < j.val then
            ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) • F.map (S.indexMap t q).op
              (F.map (S.indexMap (t ∘ q) j.succAbove).op
                (s ((t ∘ q) ∘ j.succAbove))) else 0) +
          (∑ j : Fin (p + 3), if a.val ≤ j.val ∧ j.val ≤ a.val + 2 then
            ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) • F.map (S.indexMap t q).op
              (F.map (S.indexMap (t ∘ q) j.succAbove).op
                (s ((t ∘ q) ∘ j.succAbove))) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val < a.val ∨ a.val + 2 < j.val
        · have hj' : ¬ (a.val ≤ j.val ∧ j.val ≤ a.val + 2) := by omega
          simp [hj, hj']
        · have hj' : a.val ≤ j.val ∧ j.val ≤ a.val + 2 := by omega
          simp [hj, hj']
      have houter : (∑ j : Fin (p + 3), if j.val < a.val ∨ a.val + 2 < j.val then
          ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) • F.map (S.indexMap t q).op
            (F.map (S.indexMap (t ∘ q) j.succAbove).op
              (s ((t ∘ q) ∘ j.succAbove))) else 0) =
          -S.differentialValue F p ((cechSecondSortingHom X U F S p) s) t := by
        by_cases hp : p = 0
        · subst p
          have ha0 : a.val = 0 := by obtain ⟨h, _⟩ := ha; omega
          have hh : (cechSecondSortingHom X U F S 0) s = 0 := by
            funext t'
            exact secondSortingHom_strict X U F S 0 s t' (by intro i j hij; omega)
          rw [hh, S.differentialValue_zero]
          change _ = -(0 : F.obj (op (S.W 1 t)))
          rw [neg_zero]
          apply Finset.sum_eq_zero
          intro j _
          have hj : ¬ (j.val < a.val ∨ a.val + 2 < j.val) := by omega
          simp [hj]
        · exact cechRepeatOuterFaces X U F S p (Nat.pos_of_ne_zero hp) s t ht a ha
      rw [hsplit, houter, cechRepeatCentralFaces X U F S p s t a ha]
      simp only [SiteCechComplex.differentialValue]
      abel

end AlgebraicGeometry.Scheme
