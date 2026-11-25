/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.Algebra.Polynomial.Laurent

/-! # Laurent coordinates on the projective-line overlap

## References

* Stacks Project, Tag 0BXJ, proof
* Stacks Project, Tag 0BXJ, proof, the displayed
  computation of the units on D_+(T_i T_j)
* Stacks Project, Tag 01M7
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev I := ULift.{u} (Fin 2)

private def overlapExponent (m : ℤ) : laurentExponents (Set.univ : Set I.{u}) 0 :=
  ⟨fun l ↦ if l = ⟨0⟩ then m else -m, by
    rw [sum_eq_add_of_ne (i := (⟨0⟩ : I.{u})) (j := ⟨1⟩) (by decide)]
    simp, fun l hl ↦ (hl (Set.mem_univ l)).elim⟩

private def overlapExponentEquiv : ℤ ≃ laurentExponents (Set.univ : Set I.{u}) 0 where
  toFun := overlapExponent
  invFun e := e.1 ⟨0⟩
  left_inv m := by simp [overlapExponent]
  right_inv e := by
    have hs := e.2.1
    rw [sum_eq_add_of_ne (i := (⟨0⟩ : I.{u})) (j := ⟨1⟩) (by decide)] at hs
    apply Subtype.ext
    funext l
    rcases eq_or_eq_of_ne (i := (⟨0⟩ : I.{u})) (j := ⟨1⟩) (by decide) l with rfl | rfl
    · simp [overlapExponent]
    · simp [overlapExponent]
      omega

private lemma monomial_pair (a : I.{u} → ℤ) :
    monomialToNat (ULift.{u} ℤ) a =
      X (⟨0⟩ : I.{u}) ^ (a ⟨0⟩).toNat * X (⟨1⟩ : I.{u}) ^ (a ⟨1⟩).toNat := by
  rw [monomialToNat_eq_prod]
  exact Fintype.prod_eq_mul _ _ (by decide)
    (fun l hl ↦ ((eq_or_eq_of_ne (i := (⟨0⟩ : I.{u})) (j := ⟨1⟩)
      (by decide) l).elim hl.1 hl.2).elim)

private lemma overlap_le_standard (k : Type u) [Field k] :
    overlap k ≤ standardOpen I.{u} (Spec (.of k)) ⟨0⟩ ⊓
      standardOpen I.{u} (Spec (.of k)) ⟨1⟩ := by
  exact le_inf (by simpa only [chart_singleton] using overlap_le_chart k ⟨0⟩)
    (by simpa only [chart_singleton] using overlap_le_chart k ⟨1⟩)

private lemma restrict_ratio (k : Type u) [Field k] :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_standard k)).op
        (ratio I.{u} (Spec (.of k)) ⟨0⟩ ⟨1⟩) =
      chartFun k Set.univ (awayMonomial _ _ (overlapExponent 1)) := by
  rw [map_ratio (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (⟨0⟩ : I.{u}))
    (x := monomialToNat (ULift.{u} ℤ) (Set.univ.indicator (1 : I.{u} → ℤ)))
    (by rw [monomial_pair]; simp; ring) le_rfl]
  change chartFun k Set.univ _ = chartFun k Set.univ _
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap_awayRatio]
  rw [← awayMonomial_eq (R := ULift.{u} ℤ) (overlapExponent 1) (N := 1)
    (by intro l; simp [overlapExponent]; split_ifs <;> norm_num)]
  rw [Away.val_mk]
  congr 1
  · rw [monomial_pair]
    simp [overlapExponent, pow_succ]
  · apply Subtype.ext
    rw [monomial_pair]
    simp

private lemma monomial_zpow (k : Type u) [Field k]
    (q : Γ(ProjectiveLine (Spec (.of k)), overlap k)ˣ)
    (hq : q.val = chartFun k Set.univ (awayMonomial _ _ (overlapExponent 1))) (m : ℤ) :
    (q ^ m).val = chartFun k Set.univ (awayMonomial _ _ (overlapExponent m)) := by
  have hn : q⁻¹.val = chartFun k Set.univ (awayMonomial _ _ (overlapExponent (-1))) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hq, ← map_mul, Proj.awayMonomial_mul _ _ (overlapExponent 0)]
    · rw [Proj.awayMonomial_zero _ (by ext l; simp [overlapExponent]), map_one]
    · ext l
      simp only [overlapExponent, Pi.add_apply]
      split_ifs <;> norm_num
  have hp (n : ℕ) (z : ℤ) :
      chartFun k Set.univ (awayMonomial _ _ (overlapExponent (n * z))) =
        chartFun k Set.univ (awayMonomial _ _ (overlapExponent z)) ^ n := by
    rw [Proj.awayMonomial_pow (overlapExponent z) n _ ?_, map_pow]
    ext l
    simp [overlapExponent]
  cases m with
  | ofNat n =>
    change (q ^ (n : ℤ)).val = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hq]
    simpa only [mul_one, Int.ofNat_eq_natCast] using (hp n 1).symm
  | negSucc n =>
    change (q ^ (-((n + 1 : ℕ) : ℤ))).val = _
    rw [zpow_neg, zpow_natCast, Units.inv_pow_eq_pow_inv, hn]
    simpa only [mul_neg, mul_one, Nat.cast_add, Nat.cast_one, Int.negSucc_eq] using
      (hp (n + 1) (-1)).symm

private lemma bijective_eval_overlap (k : Type u) [Field k]
    (q : Γ(ProjectiveLine (Spec (.of k)), overlap k)ˣ)
    (hq : q.val = chartFun k Set.univ (awayMonomial _ _ (overlapExponent 1))) :
    Function.Bijective (LaurentPolynomial.eval₂ (chartConst k (overlap k)) q) := by
  classical
  have hB := bijective_sum_awayMonomial (n := I.{u}) k
    (Set.univ_nonempty (α := I.{u}))
  let g : LaurentPolynomial k ≃ (laurentExponents (Set.univ : Set I.{u}) 0 →₀ k) :=
    (AddMonoidAlgebra.coeffEquiv (R := k) (M := ℤ)).trans
      (Finsupp.equivCongrLeft overlapExponentEquiv)
  convert hB.comp g.bijective using 1
  funext p
  simp only [Function.comp_apply, g, Equiv.trans_apply, AddMonoidAlgebra.coeffEquiv_apply,
    Finsupp.equivCongrLeft_apply, Finsupp.sum_equivMapDomain]
  change LaurentPolynomial.eval₂ (chartConst k (overlap k)) q p =
    p.coeff.sum (fun m a ↦ chartConst k (overlap k) a *
      chartFun k Set.univ (awayMonomial _ _ (overlapExponent m)))
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro m a
  rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T,
    monomial_zpow k q hq]

/-- Laurent evaluation at x_0/x_1 identifies the overlap ring with k[z,z^-1]. -/
theorem bijective_overlap_laurent (k : Type u) [Field k] :
    Function.Bijective
      (LaurentPolynomial.eval₂
        (chartConst k (standardOpen _ (Spec (.of k)) (⟨0⟩ : ULift.{u} (Fin 2)) ⊓
          standardOpen _ (Spec (.of k)) (⟨1⟩ : ULift.{u} (Fin 2))))
        (ratioUnit (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ⟨1⟩)) := by
  let V := standardOpen I.{u} (Spec (.of k)) ⟨0⟩ ⊓
    standardOpen I.{u} (Spec (.of k)) ⟨1⟩
  let ρ := (ProjectiveLine (Spec (.of k))).presheaf.map
    (homOfLE (overlap_le_standard k)).op
  have hV : overlap k = V := by
    apply le_antisymm (overlap_le_standard k)
    exact le_overlap k (i := ⟨0⟩) (j := ⟨1⟩) (by decide)
      (by simpa only [chart_singleton] using (inf_le_left : V ≤ _))
      (by simpa only [chart_singleton] using (inf_le_right : V ≤ _))
  have hρ : Function.Bijective ρ := by
    have : IsIso (homOfLE (overlap_le_standard k)).op := by
      rw [show homOfLE (overlap_le_standard k) = eqToHom hV from Subsingleton.elim _ _]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ρ
  apply Function.Bijective.of_comp_left (hf := hρ.injective)
  let q := Units.map ρ.hom.toMonoidHom (ratioUnit I.{u} (Spec (.of k)) ⟨0⟩ ⟨1⟩)
  have hq : q.val = chartFun k Set.univ (awayMonomial _ _ (overlapExponent 1)) :=
    restrict_ratio k
  convert bijective_eval_overlap k q hq using 1
  funext p
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => simp only [Function.comp_apply, map_add] at *; rw [hp, hr]
  | C_mul_T m a =>
    simp only [Function.comp_apply]
    rw [LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, map_mul]
    congr 1
    · exact presheaf_map_chartConst k (overlap_le_standard k) a
    · exact congrArg Units.val (map_zpow (Units.map ρ.hom.toMonoidHom)
        (ratioUnit I.{u} (Spec (.of k)) ⟨0⟩ ⟨1⟩) m)

end AlgebraicGeometry.ProjectiveLine
