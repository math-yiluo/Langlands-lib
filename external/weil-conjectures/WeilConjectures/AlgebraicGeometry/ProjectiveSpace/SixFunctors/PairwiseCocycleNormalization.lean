/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.PairwiseLaurentUnitExpansion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials

/-! # Cocycle comparison for pairwise Laurent expansions

## References

* Stacks Project, Tag 0BXJ, the triple-overlap calculation
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev torus {n : Type u} [Fintype n] (k : Type u) [Field k] :=
  toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n Set.univ

private def constMap {n : Type u} (k : Type u) [Field k]
    (V : ℙ(n; Spec (.of k)).Opens) : k →+* Γ(ℙ(n; Spec (.of k)), V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
    (ℙ(n; Spec (.of k))).presheaf.map (homOfLE le_top).op).hom

private def torusMap {n : Type u} [Fintype n] (k : Type u) [Field k] :
    Away (homogeneousSubmodule n (ULift.{u} ℤ))
      (monomialToNat (ULift.{u} ℤ) (Set.univ.indicator (1 : n → ℤ))) →+*
      Γ(ℙ(n; Spec (.of k)), torus (n := n) k) :=
  (Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE
    (basicOpenInt n Set.univ) (torus k) le_rfl).hom

private def ratioExponent {n : Type u} [Fintype n] [DecidableEq n]
    (i j : n) (d : ℤ) : laurentExponents (Set.univ : Set n) 0 :=
  ⟨Pi.single i d - Pi.single j d, by simp [Finset.sum_sub_distrib],
    fun l hl ↦ (hl (Set.mem_univ l)).elim⟩

private lemma torus_le {n : Type u} [Fintype n] (k : Type u) [Field k] (i : n) :
    torus k ≤ standardOpen n (Spec (.of k)) i := by
  intro x hx
  exact (Proj.mem_basicOpen_monomialToNat_indicator.mp hx) i (Set.mem_univ i)

private lemma map_constMap {n : Type u} (k : Type u) [Field k]
    {V W : ℙ(n; Spec (.of k)).Opens} (h : W ≤ V) (c : k) :
    (ℙ(n; Spec (.of k))).presheaf.map (homOfLE h).op (constMap k V c) =
      constMap k W c := by
  simp only [constMap, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.presheaf_map_map_apply]
  rfl

private lemma monomial_single {n : Type u} [Fintype n] [DecidableEq n] (i : n) :
    monomialToNat (ULift.{u} ℤ) (Pi.single i (1 : ℤ)) = X i := by
  rw [monomialToNat_eq_prod, Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

private lemma torus_ratio {n : Type u} [Fintype n] [DecidableEq n]
    (k : Type u) [Field k] (i j : n) :
    (ℙ(n; Spec (.of k))).presheaf.map
        (homOfLE (le_inf (torus_le k i) (torus_le k j))).op (ratio n (Spec (.of k)) i j) =
      torusMap k (awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent i j 1)) := by
  let b : n → ℤ := 1 - Pi.single j 1
  have hb : 0 ≤ b := by
    intro l
    simp only [b, Pi.sub_apply, Pi.one_apply, Pi.single_apply]
    split_ifs <;> norm_num
  have hsingle (l : n) : 0 ≤ (Pi.single l (1 : ℤ) : n → ℤ) :=
    Pi.single_nonneg.mpr (by norm_num)
  have hx : monomialToNat (ULift.{u} ℤ) (Set.univ.indicator (1 : n → ℤ)) =
      X j * monomialToNat (ULift.{u} ℤ) b := by
    rw [← monomial_single j, monomialToNat_mul (hsingle j) hb]
    congr 1
    ext l
    simp [b]
  rw [map_ratio (monomialToNat_mem b) hx le_rfl]
  change torusMap k _ = torusMap k _
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap_awayRatio]
  rw [← awayMonomial_eq (R := ULift.{u} ℤ) (ratioExponent i j 1) (N := 1)
    (by intro l; simp only [ratioExponent, Pi.sub_apply, Pi.single_apply];
        split_ifs <;> norm_num)]
  rw [Away.val_mk]
  congr 1
  · rw [← monomial_single i, monomialToNat_mul (hsingle i) hb]
    congr 1
    ext l
    simp [b, ratioExponent]
    ring
  · apply Subtype.ext
    simp

private lemma torus_transition {n : Type u} [Fintype n] [DecidableEq n]
    (k : Type u) [Field k] (i j : n) (d : ℤ) :
    (ℙ(n; Spec (.of k))).presheaf.map
        (homOfLE (le_inf (torus_le k i) (torus_le k j))).op
        (transitionUnit n (Spec (.of k)) d i j).val =
      torusMap k (awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent i j d)) := by
  let ρ := (ℙ(n; Spec (.of k))).presheaf.map
    (homOfLE (le_inf (torus_le k i) (torus_le k j))).op
  let q := Units.map ρ.hom.toMonoidHom (ratioUnit n (Spec (.of k)) i j)
  have hq : q.val = torusMap k (awayMonomial _ _ (ratioExponent i j 1)) :=
    torus_ratio k i j
  have hn : q⁻¹.val = torusMap k (awayMonomial _ _ (ratioExponent i j (-1))) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hq, ← map_mul, Proj.awayMonomial_mul _ _ (ratioExponent i j 0)]
    · rw [Proj.awayMonomial_zero _ (by ext l; simp [ratioExponent]), map_one]
    · ext l
      simp only [ratioExponent, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> norm_num
  have hp (m : ℕ) (z : ℤ) :
      torusMap k (awayMonomial _ _ (ratioExponent i j (m * z))) =
        torusMap k (awayMonomial _ _ (ratioExponent i j z)) ^ m := by
    rw [Proj.awayMonomial_pow (ratioExponent i j z) m _ ?_, map_pow]
    ext l
    simp only [ratioExponent, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, nsmul_eq_mul]
    split_ifs <;> ring
  change (Units.map ρ.hom.toMonoidHom
    (ratioUnit n (Spec (.of k)) i j ^ d)).val = _
  rw [map_zpow]
  change (q ^ d).val = _
  cases d with
  | ofNat m =>
    change (q ^ (m : ℤ)).val = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hq]
    simpa only [mul_one, Int.ofNat_eq_natCast] using (hp m 1).symm
  | negSucc m =>
    change (q ^ (-((m + 1 : ℕ) : ℤ))).val = _
    rw [zpow_neg, zpow_natCast, Units.inv_pow_eq_pow_inv, hn]
    simpa only [mul_neg, mul_one, Nat.cast_add, Nat.cast_one, Int.negSucc_eq] using
      (hp (m + 1) (-1)).symm

private def addExponent {n : Type u} [Fintype n]
    (e f : laurentExponents (Set.univ : Set n) 0) :
    laurentExponents (Set.univ : Set n) 0 :=
  ⟨e.1 + f.1, by simp [Finset.sum_add_distrib, e.2.1, f.2.1],
    fun l hl ↦ (hl (Set.mem_univ l)).elim⟩

private lemma torus_monomial_injective {n : Type u} [Fintype n] [Nonempty n]
    (k : Type u) [Field k] (e f : laurentExponents (Set.univ : Set n) 0)
    (a b : k) (ha : a ≠ 0)
    (h : constMap k (torus k) a * torusMap k (awayMonomial _ _ e) =
      constMap k (torus k) b * torusMap k (awayMonomial _ _ f)) :
    e = f ∧ a = b := by
  classical
  have hs : Finsupp.single e a = Finsupp.single f b := by
    apply (bijective_sum_awayMonomial (n := n) k Set.univ_nonempty).injective
    simpa only [Finsupp.sum_single_index, map_zero, zero_mul, constMap, torusMap,
      CommRingCat.Hom.hom] using h
  exact ((Finsupp.single_eq_single_iff e f a b).mp hs).resolve_right (fun hz ↦ ha hz.1)

private lemma restrict_constUnit (k : Type u) [Field k] (r : ℕ)
    (i : ULift.{u} (Fin r)) (c : kˣ) (W : ℙ(ULift.{u} (Fin r); Spec (.of k)).Opens)
    (hi : W ≤ standardOpen _ (Spec (.of k)) i) :
    (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map (homOfLE hi).op
        (standardOpenConstUnit k r i c).val = constMap k W c := by
  exact map_constMap k hi c

-- Preserve the named nondependent binders in the existing public statement.
set_option linter.unusedVariables false in
/-- The cocycle equation makes the exponents in pairwise Laurent expansions
constant and the scalar coefficients a chart coboundary.
-/
theorem exists_standardUnitCocycle_normalization_of_pairwise_laurent
    (k : Type u) [Field k] (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ)
    (ht : ∀ (i j l : ULift.{u} (Fin r))
      (W : ℙ(ULift.{u} (Fin r); Spec (.of k)).Opens)
      (hi : W ≤ standardOpen _ (Spec (.of k)) i)
      (hj : W ≤ standardOpen _ (Spec (.of k)) j)
      (hl : W ≤ standardOpen _ (Spec (.of k)) l),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hj)).op (t i j).val *
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hj hl)).op (t j l).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hl)).op (t i l).val)
    (e : ∀ i j : ULift.{u} (Fin r), ℤ)
    (c : ∀ i j : ULift.{u} (Fin r), kˣ)
    (hpair : ∀ i j : ULift.{u} (Fin r), i ≠ j →
      (t i j).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (standardOpenConstUnit k r i (c i j)).val *
          (transitionUnit _ (Spec (.of k)) (e i j) i j).val) :
    ∃ d : ℤ, ∃ a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ,
      ∀ i j : ULift.{u} (Fin r), i ≠ j →
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_left).op (a i).val * (t i j).val =
          (transitionUnit _ (Spec (.of k)) d i j).val *
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_right).op (a j).val := by
  classical
  let I := ULift.{u} (Fin r)
  let b : I := ⟨⟨0, by omega⟩⟩
  let q : I := ⟨⟨1, by omega⟩⟩
  have hbq : b ≠ q := by
    intro h
    have hval := congrArg (fun x : I ↦ x.down.val) h
    change 0 = 1 at hval
    omega
  have : Nonempty I := ⟨b⟩
  have hrest (i j : I) (hij : i ≠ j) :
      (ℙ(I; Spec (.of k))).presheaf.map
          (homOfLE (le_inf (torus_le k i) (torus_le k j))).op (t i j).val =
        constMap k (torus k) (c i j) *
          torusMap k (awayMonomial _ _ (ratioExponent i j (e i j))) := by
    rw [hpair i j hij, map_mul, Scheme.presheaf_map_map_apply, homOfLE_comp,
      restrict_constUnit, torus_transition]
  -- Compare the three monomials on the full coordinate torus.
  have htriple (i j l : I) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
      e i j = e i l ∧ e j l = e i l ∧ c i j * c j l = c i l := by
    have h := ht i j l (torus k) (torus_le k i) (torus_le k j) (torus_le k l)
    rw [hrest i j hij, hrest j l hjl, hrest i l hil] at h
    have hm := torus_monomial_injective k
      (addExponent (ratioExponent i j (e i j)) (ratioExponent j l (e j l)))
      (ratioExponent i l (e i l)) ((c i j * c j l : kˣ) : k) (c i l)
      (Units.ne_zero _) (by
        rw [Units.val_mul, map_mul, ← Proj.awayMonomial_mul _ _
          (addExponent (ratioExponent i j (e i j)) (ratioExponent j l (e j l))) rfl,
          map_mul]
        convert h using 1; ring)
    have hi := congrArg (fun v ↦ v.1 i) hm.1
    have hl := congrArg (fun v ↦ v.1 l) hm.1
    simp only [addExponent, ratioExponent, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
      ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne, sub_zero, hil, sub_self, add_zero,
      hil.symm, hjl.symm, zero_sub, zero_add, neg_inj] at hi hl
    exact ⟨hi, by omega, Units.ext hm.2⟩
  have third (i j : I) : ∃ l : I, l ≠ i ∧ l ≠ j := by
    let z : I := ⟨⟨2, by omega⟩⟩
    have hbz : b ≠ z := by
      intro h
      have hval := congrArg (fun x : I ↦ x.down.val) h
      change 0 = 2 at hval
      omega
    have hqz : q ≠ z := by
      intro h
      have hval := congrArg (fun x : I ↦ x.down.val) h
      change 1 = 2 at hval
      omega
    by_cases hbi : b = i
    · subst i
      by_cases hqj : q = j
      · exact ⟨z, hbz.symm, hqj ▸ hqz.symm⟩
      · exact ⟨q, hbq.symm, hqj⟩
    · by_cases hbj : b = j
      · subst j
        by_cases hqi : q = i
        · exact ⟨z, hqi ▸ hqz.symm, hbz.symm⟩
        · exact ⟨q, hqi, hbq.symm⟩
      · exact ⟨b, hbi, hbj⟩
  -- Propagate the triple equalities to all ordered pairs.
  have hrow (i j l : I) (hij : i ≠ j) (hil : i ≠ l) : e i j = e i l := by
    by_cases hjl : j = l
    · rw [hjl]
    · exact (htriple i j l hij hil hjl).1
  have hsym (i j : I) (hij : i ≠ j) : e i j = e j i := by
    obtain ⟨l, hli, hlj⟩ := third i j
    exact ((htriple i j l hij hli.symm hlj.symm).1.trans
      (htriple i j l hij hli.symm hlj.symm).2.1.symm).trans
      (hrow j l i hlj.symm hij.symm)
  have he (i j : I) (hij : i ≠ j) : e i j = e b q := by
    by_cases hib : i = b
    · subst i
      exact hrow b j q hij hbq
    · exact (hrow i j b hij hib).trans
        ((hsym i b hib).trans (hrow b i q (Ne.symm hib) hbq))
  have hinv (i j : I) (hij : i ≠ j) : c i j * c j i = 1 := by
    obtain ⟨l, hli, hlj⟩ := third i j
    apply mul_right_cancel (b := c i l)
    rw [one_mul, mul_assoc, (htriple j i l hij.symm hlj.symm hli.symm).2.2,
      (htriple i j l hij hli.symm hlj.symm).2.2]
  -- Trivialize the scalar cocycle explicitly at the base chart b.
  let a : I → kˣ := fun i ↦ if i = b then 1 else (c i b)⁻¹
  have ha (i j : I) (hij : i ≠ j) : a i * c i j = a j := by
    by_cases hib : i = b
    · subst i
      simp only [a, ite_eq_left rfl, ite_eq_right hij.symm, one_mul]
      exact eq_inv_of_mul_eq_one_left (hinv b j hij)
    · by_cases hjb : j = b
      · subst j
        simp [a, hib]
      · have hc := (htriple i j b hij hib hjb).2.2
        simp only [a, ite_eq_right hib, ite_eq_right hjb]
        apply mul_right_cancel (b := c j b)
        rw [mul_assoc, hc, inv_mul_cancel, inv_mul_cancel]
  refine ⟨e b q, fun i ↦ standardOpenConstUnit k r i (a i), ?_⟩
  intro i j hij
  rw [restrict_constUnit, restrict_constUnit, hpair i j hij, restrict_constUnit, he i j hij,
    ← mul_assoc, ← map_mul, ← Units.val_mul, ha i j hij, mul_comm]

end

end AlgebraicGeometry.ProjectiveSpace
