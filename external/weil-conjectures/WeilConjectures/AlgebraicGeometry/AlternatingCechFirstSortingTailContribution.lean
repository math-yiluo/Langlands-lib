/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortUnique
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortAdvance

/-!
# Tail junction deletions in the first sorting homotopy

Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-tail-contribution)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
private theorem tail_position_ge {p : ℕ} (σ τ : Equiv.Perm (Fin (p + 2)))
    (a : Fin (p + 2)) (hτ : cechPartialSort σ τ a) :
    a ≤ τ.symm (σ a) := by
  by_contra h
  have hb : (τ.symm (σ a)).val < a.val := lt_of_not_ge h
  have he := hτ.1 _ hb
  rw [τ.apply_symm_apply] at he
  have := σ.injective he
  omega

private theorem tail_position_iff {p : ℕ} (σ τ : Equiv.Perm (Fin (p + 2)))
    (a : Fin (p + 2)) (r : Fin (p + 3)) (hτ : cechPartialSort σ τ a) :
    cechJunction σ τ a r = σ a ∧ a.val < r.val ↔
      r = (τ.symm (σ a)).succ := by
  have hb := tail_position_ge σ τ a hτ
  constructor
  · rintro ⟨he, hr⟩
    simp only [cechJunction, not_le.mpr hr, dite_false] at he
    have hv := congrArg Fin.val (τ.injective (he.trans (τ.apply_symm_apply _).symm))
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp only at hv
    omega
  · intro he
    subst r
    constructor
    · simp only [cechJunction, Fin.val_succ]
      rw [dite_eq_right (by omega)]
      convert τ.apply_symm_apply (σ a) using 2
      apply Fin.ext
      simp
    · simp only [Fin.val_succ]
      exact Nat.lt_succ_of_le hb

private theorem tail_coefficient {p : ℕ} (σ τ ρ : Equiv.Perm (Fin (p + 2)))
    (a : Fin (p + 2)) (hτ : cechPartialSort σ τ a)
    (hρ : ρ = τ * (Fin.cycleIcc a (τ.symm (σ a))).symm) :
    ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) *
      (-1 : ℤ) ^ (τ.symm (σ a)).succ.val = -(Equiv.Perm.sign ρ : ℤ) := by
  have hb := tail_position_ge σ τ a hτ
  have hs : (Equiv.Perm.sign ρ : ℤ) =
      (Equiv.Perm.sign τ : ℤ) * (-1 : ℤ) ^ ((τ.symm (σ a)).val - a.val) := by
    rw [hρ, map_mul, Equiv.Perm.sign_symm, Fin.sign_cycleIcc_of_le hb]
    simp
  rw [hs]
  simp only [Fin.val_succ, pow_succ]
  have hp : (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ (τ.symm (σ a)).val =
      (-1 : ℤ) ^ ((τ.symm (σ a)).val - a.val) := by
    have he : (τ.symm (σ a)).val = a.val + ((τ.symm (σ a)).val - a.val) := by
      omega
    conv_lhs => rhs; rw [he, pow_add]
    rw [← mul_assoc, ← pow_add]
    simp [← two_mul, pow_mul]
  calc
    _ = -(((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ (τ.symm (σ a)).val) *
        (Equiv.Perm.sign τ : ℤ)) := by ring
    _ = _ := by rw [hp]; ring

private theorem tail_transport (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I)
    (q : Fin (p + 3) → Fin (p + 2)) (r : Fin (p + 3))
    (ρ : Equiv.Perm (Fin (p + 2))) (he : q ∘ r.succAbove = ρ) :
    F.map (S.indexMap t q).op
      (F.map (S.indexMap (t ∘ q) r.succAbove).op
        (s ((t ∘ q) ∘ r.succAbove))) =
      F.map (S.indexMap t ρ).op (s (t ∘ ρ)) := by
  have hm : S.indexMap t q ≫ S.indexMap (t ∘ q) r.succAbove =
      S.indexMap t (q ∘ r.succAbove) := Subsingleton.elim _ _
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, hm]
  exact congrArg (fun α : Fin (p + 2) → Fin (p + 2) =>
    F.map (S.indexMap t α).op (s (t ∘ α))) he

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem tail_stage (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I)
    (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2)) :
    (∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if (cechPartialSort σ τ a ∧ cechJunction σ τ a r = σ a) ∧ a.val < r.val then
        ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
          F.map (S.indexMap t (cechJunction σ τ a)).op
            ((-1 : ℤ) ^ r.val •
              F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
                (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove))) else 0) =
      -(∑ ρ : Equiv.Perm (Fin (p + 2)),
        if (∀ k, k.val < a.val + 1 → ρ k = σ k) ∧
          (∀ i j, a.val + 1 ≤ i.val → i < j → ρ i < ρ j) then
          (Equiv.Perm.sign ρ : ℤ) • F.map (S.indexMap t ρ).op (s (t ∘ ρ)) else 0) := by
  obtain ⟨τ₀, hτ, uτ⟩ := cechPartialSort_existsUnique (p + 2) σ a.val (by omega)
  obtain ⟨ρ₀, hρ, uρ⟩ := cechPartialSort_existsUnique (p + 2) σ (a.val + 1) (by omega)
  have ht (τ : Equiv.Perm (Fin (p + 2))) : cechPartialSort σ τ a ↔ τ = τ₀ :=
    ⟨fun h => uτ τ h, fun h => h ▸ hτ⟩
  have hr (ρ : Equiv.Perm (Fin (p + 2))) :
      ((∀ k, k.val < a.val + 1 → ρ k = σ k) ∧
        (∀ i j, a.val + 1 ≤ i.val → i < j → ρ i < ρ j)) ↔ ρ = ρ₀ :=
    ⟨fun h => uρ ρ h, fun h => h ▸ hρ⟩
  have hf (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) :
      ((cechPartialSort σ τ a ∧ cechJunction σ τ a r = σ a) ∧ a.val < r.val) ↔
        τ = τ₀ ∧ r = (τ₀.symm (σ a)).succ := by
    constructor
    · rintro ⟨⟨h, he⟩, hl⟩
      have ht' := (ht τ).mp h
      subst τ
      exact ⟨rfl, (tail_position_iff σ _ a r hτ).mp ⟨he, hl⟩⟩
    · rintro ⟨rfl, he⟩
      obtain ⟨hj, hl⟩ := (tail_position_iff σ _ a r hτ).mpr he
      exact ⟨⟨hτ, hj⟩, hl⟩
  simp_rw [hf, hr, ite_and, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  obtain ⟨he, hc⟩ := cechPartialSort_advance p σ τ₀ ρ₀ a hτ hρ
  rw [map_zsmul, smul_smul, tail_transport X U F S p s t _ _ ρ₀ he,
    tail_coefficient σ τ₀ ρ₀ a hτ hc, neg_smul]

open Classical in
/-- Tail-labelled junction deletions contribute the negatives of the advanced stages.
Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.

Proof: For each fixed sigma and a, the permutation satisfying the partial
sorting filter is unique: its prefix is sigma below a and its tail is the
increasing enumeration of the unused labels. The same construction defines
the unique partial permutation rho at stage a+1 (including stage p+2).
Let tau be the stage-a permutation and b = tau.symm (sigma a). Then b >= a,
since a label in the fixed prefix cannot equal sigma a by injectivity.
The tail junction label sigma a occurs exactly at r = b+1. Removing that
position leaves rho, obtained from tau by moving the entry at b to a and
shifting entries a through b-1 one place right. This fixes sigma through a
and leaves the remaining tail increasing. This move has sign (-1)^(b-a),
including b=a when it is the identity. Thus sign(rho) = (-1)^(b-a) sign(tau).
The deletion coefficient (-1)^a (-1)^(b+1) sign(tau) equals -sign(rho),
because a+b+1 and b-a+1 differ by 2a. The two index maps compose to the
index map of the deleted tuple since morphisms of opens form a subsingleton.
Use the tuple equality to identify this with the map for rho. Functoriality and additivity of F
therefore turn the unique tail term into the negative stage-a+1 term.
Apply this for each sigma, retaining its stable sorting filter on both sides,
and sum over a and sigma. At the last a, tau=rho=sigma and b=a, so the same
argument still applies. Labels, rather than their values in I, are compared,
so repetitions in t cause no extra terms; an empty I admits no such t.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-tail-contribution) -/
theorem cechFirstSortingJunctionTailContribution (X : Scheme.{u}) {I : Type v}
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
    let T := ∑ σ, ∑ a, ∑ τ, ∑ r,
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ a.val < r.val then E σ a τ r else 0
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ, ∑ τ, if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    T = - ∑ a : Fin (p + 2), B (a.val + 1) t := by
  classical
  dsimp only
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hs : cechStableSort t σ
  · simp only [hs, true_and]
    exact tail_stage X U F S p s t σ a
  · simp [hs]
end AlgebraicGeometry.Scheme
