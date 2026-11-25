/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# Prefix contributions in the first sorting homotopy

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-prefix-contribution)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem prefix_junction_delete {p : ℕ}
    (σ τ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
    (h : cechPartialSort σ τ a) :
    cechJunction σ τ a ∘ a.castSucc.succAbove = τ := by
  funext k
  simp only [Function.comp_apply]
  by_cases hk : k < a
  · rw [Fin.succAbove_castSucc_of_lt a k hk]
    simp only [cechJunction, Fin.val_castSucc,
      show k.val ≤ a.val from Nat.le_of_lt hk, dite_true]
    exact (h.1 k hk).symm
  · rw [Fin.succAbove_castSucc_of_le a k (le_of_not_gt hk)]
    simp only [cechJunction, Fin.val_succ,
      show ¬ k.val + 1 ≤ a.val by omega, dite_false]
    congr 1

private theorem prefix_junction_filter {p : ℕ}
    (σ τ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2)) (r : Fin (p + 3)) :
    (cechJunction σ τ a r = σ a ∧ r.val ≤ a.val) ↔ r = a.castSucc := by
  constructor
  · rintro ⟨he, hr⟩
    simp only [cechJunction, hr, dite_true] at he
    have he' := σ.injective he
    apply Fin.ext
    exact congrArg (fun k : Fin (p + 2) ↦ k.val) he'
  · rintro rfl
    simp [cechJunction]

open Classical in
/-- Prefix-labelled junction deletions contribute the unadvanced partial sorting stages.
Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.

Proof: Fix sigma, a and a partial sorting permutation tau. In the prefix of
q = cechJunction sigma tau a, q(r) = sigma(r). Injectivity of sigma shows
that q(r) = sigma(a) and r <= a hold exactly when r = a. Removing this
position gives q composed with a.succAbove = tau: below a this uses the
fixed-prefix condition, and at and above a it uses the tail branch of q.
The composite of the two index maps is the index map for tau because
X.Opens is a thin category, so parallel morphisms are equal. Apply functoriality
of F and move integer scalar
multiplication through its additive maps. The two powers (-1)^a multiply
to 1, so the remaining term is sign(tau) times the restriction along tau.
For a pair failing the stable or partial sorting filter, both contributions
are zero. The partial sorting filter is exactly the filter defining B(a).
Summing these identities over r, tau, a and sigma, and commuting the sigma
and a sums, gives the claimed equality. No uniqueness of stable sorting is
needed here. Repeated values of t are harmless since deletion uses labels.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-prefix-contribution) -/
theorem cechFirstSortingJunctionPrefixContribution (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) :
    let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
        (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
      ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
        F.map (S.indexMap t (cechJunction σ τ a)).op
          ((-1 : ℤ) ^ r.val •
            F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
              (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
    let P := ∑ σ, ∑ a, ∑ τ, ∑ r,
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ r.val ≤ a.val then E σ a τ r else 0
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ, ∑ τ, if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    P = ∑ a : Fin (p + 2), B a.val t := by
  classical
  dsimp only
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  by_cases h : cechStableSort t σ ∧ cechPartialSort σ τ a
  · have hfilter (r : Fin (p + 3)) :
        (((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ r.val ≤ a.val) ↔ r = a.castSucc := by
      simpa only [h, true_and] using prefix_junction_filter σ τ a r
    simp only [hfilter, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hh : cechJunction σ τ a ∘ a.castSucc.succAbove = τ :=
      prefix_junction_delete σ τ a h.2
    have hcomp :
        F.map (S.indexMap t (cechJunction σ τ a)).op
            (F.map (S.indexMap (t ∘ cechJunction σ τ a)
              a.castSucc.succAbove).op
              (s ((t ∘ cechJunction σ τ a) ∘ a.castSucc.succAbove))) =
          F.map (S.indexMap t
            (cechJunction σ τ a ∘ a.castSucc.succAbove)).op
            (s (t ∘ (cechJunction σ τ a ∘ a.castSucc.succAbove))) := by
      have hm : (S.indexMap t
          (cechJunction σ τ a ∘ a.castSucc.succAbove)).op =
          (S.indexMap (t ∘ cechJunction σ τ a)
            a.castSucc.succAbove).op ≫
            (S.indexMap t (cechJunction σ τ a)).op := Subsingleton.elim _ _
      rw [hm, F.map_comp]
      rfl
    simp only [map_zsmul, hcomp, Fin.val_castSucc,
      smul_smul]
    have hsquare : (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ a.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hcoeff : ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) *
        (-1 : ℤ) ^ a.val = (Equiv.Perm.sign τ : ℤ) := by
      calc
        _ = ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ a.val) *
            (Equiv.Perm.sign τ : ℤ) := by ring
        _ = _ := by rw [hsquare, one_mul]
    rw [hcoeff, hh]
    exact (ite_eq_left h).symm
  · have h' : ¬ (cechStableSort t σ ∧
        (∀ k, k.val < a.val → τ k = σ k) ∧
        (∀ i j, a.val ≤ i.val → i < j → τ i < τ j)) := h
    simp only [h', ite_false]
    apply Finset.sum_eq_zero
    intro r _
    have hn : ¬ (((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
        cechJunction σ τ a r = σ a) ∧ r.val ≤ a.val) := fun hr ↦ h hr.1.1
    simp only [hn, ite_false]

end AlgebraicGeometry.Scheme
