/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundary
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Division

/-! # Pairwise Laurent expansions on projective-space overlaps

## References

* Stacks Project, Tag 0BXJ, the double-overlap calculation
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

variable (k : Type u) [Field k] (r : ℕ)

/-- The structural constant map from the base field to sections on a standard open. -/
def standardOpenConst (i : ULift.{u} (Fin r)) :
    k →+* Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
      standardOpen _ (Spec (.of k)) i) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫
    (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)).appTop ≫
    (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map (homOfLE le_top).op).hom

/-- The unit induced by a nonzero constant on a standard chart. -/
def standardOpenConstUnit (i : ULift.{u} (Fin r)) (c : kˣ) :
    Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
      standardOpen _ (Spec (.of k)) i)ˣ :=
  Units.map (standardOpenConst k r i).toMonoidHom c

private theorem exists_unit_zpow_of_localization
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (p : R) [IsLocalization.Away p S] (hp : Prime p)
    (q : Sˣ) (hq : q.val = algebraMap R S p) (u : Sˣ) :
    ∃ (v : Rˣ) (m : ℤ), u = Units.map (algebraMap R S).toMonoidHom v * q ^ m := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj p (u.val : S)
  have hau : IsUnit (algebraMap R S a) := by
    rw [← ha, ← hq]
    exact u.isUnit.mul (q.isUnit.pow n)
  obtain ⟨N, hN⟩ := (IsLocalization.Away.algebraMap_isUnit_iff p).mp hau
  obtain ⟨m, _, hm⟩ := (dvd_prime_pow hp N).mp hN
  obtain ⟨v, hv⟩ := hm.symm
  have h : u * q ^ n = Units.map (algebraMap R S).toMonoidHom v * q ^ m := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map]
    rw [hq, ha, ← hv, map_mul, map_pow, mul_comm]
    rfl
  refine ⟨v, (m : ℤ) - n, ?_⟩
  calc
    u = (u * q ^ n) * (q ^ n)⁻¹ := by group
    _ = (Units.map (algebraMap R S).toMonoidHom v * q ^ m) * (q ^ n)⁻¹ := by rw [h]
    _ = Units.map (algebraMap R S).toMonoidHom v * q ^ ((m : ℤ) - n) := by
      rw [zpow_sub, zpow_natCast, zpow_natCast, mul_assoc]

private theorem exists_overlap_unit_expansion
    (i j : ULift.{u} (Fin r)) (hij : i ≠ j)
    (t : Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
      standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ) :
    ∃ (m : ℤ) (c : kˣ), t.val =
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
        (homOfLE inf_le_left).op (standardOpenConstUnit k r i c).val *
          (transitionUnit _ (Spec (.of k)) m i j).val := by
  let n := ULift.{u} (Fin r)
  let X := ℙ(n; Spec (.of k))
  let U := standardOpen n (Spec (.of k)) j
  let V := standardOpen n (Spec (.of k)) i ⊓ U
  let E := chartRingEquiv n k j
  let R := Γ(X, U)
  let S := Γ(X, V)
  let p : R := coordRatio n (Spec (.of k)) j i
  let ρ : R →+* S := (X.presheaf.map (homOfLE inf_le_right).op).hom
  let : Algebra R S := ρ.toAlgebra
  let : IsDomain R := E.symm.toMulEquiv.isDomain _
  have hp : Prime p := by
    have h := (MulEquiv.prime_iff E).mpr (MvPolynomial.X_prime (i := ⟨i, hij⟩) (R := k))
    simpa only [E, chartRingEquiv_X] using h
  let : IsLocalization.Away p S :=
    (isAffineOpen_standardOpen n (Spec (.of k)) j).isLocalization_of_eq_basicOpen p
      (homOfLE inf_le_right) (by rw [basicOpen_coordRatio, inf_comm])
  let q : Sˣ := ratioUnit n (Spec (.of k)) i j
  have hq : q.val = algebraMap R S p := rfl
  obtain ⟨v, m, ht⟩ := exists_unit_zpow_of_localization p hp q hq t
  have hv : IsUnit (E.symm v.val) := v.isUnit.map E.symm.toRingHom
  obtain ⟨c, hc, hvc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hv
  obtain ⟨c, rfl⟩ := hc
  have hv' : v.val = E (MvPolynomial.C c.val) := E.symm.injective (by simpa using hvc)
  refine ⟨m, c, ?_⟩
  have hconst : ρ v.val = X.presheaf.map (homOfLE inf_le_left).op
      (standardOpenConstUnit k r i c).val := by
    rw [hv', chartRingEquiv_C]
    change ((X ↘ Spec (.of k)).specStructureMap U ≫
        X.presheaf.map (homOfLE inf_le_right).op) c.val =
      ((X ↘ Spec (.of k)).specStructureMap (standardOpen n (Spec (.of k)) i) ≫
        X.presheaf.map (homOfLE inf_le_left).op) c.val
    rw [Scheme.Hom.specStructureMap_map, Scheme.Hom.specStructureMap_map]
  have hval := congrArg Units.val ht
  change t.val = ρ v.val * (q ^ m).val at hval
  rw [hconst] at hval
  exact hval

set_option linter.unusedVariables false in
/-- Every unit on a distinct standard overlap has one Laurent exponent and a scalar
coefficient.  This is the pairwise Laurent-polynomial calculation used by the
normalization theorem.
-/
theorem exists_pairwise_laurent_unit_expansion (k : Type u) [Field k]
    (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ) :
    ∃ e : ∀ i j : ULift.{u} (Fin r), ℤ,
      ∃ c : ∀ i j : ULift.{u} (Fin r), kˣ,
        ∀ i j : ULift.{u} (Fin r), i ≠ j →
          (t i j).val =
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_left).op (standardOpenConstUnit k r i (c i j)).val *
              (transitionUnit _ (Spec (.of k)) (e i j) i j).val := by
  classical
  have h (i j : ULift.{u} (Fin r)) : ∃ (m : ℤ) (c : kˣ), i ≠ j →
      (t i j).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (standardOpenConstUnit k r i c).val *
          (transitionUnit _ (Spec (.of k)) m i j).val := by
    by_cases hij : i = j
    · exact ⟨0, 1, fun h ↦ (h hij).elim⟩
    · obtain ⟨m, c, hmc⟩ := exists_overlap_unit_expansion k r i j hij (t i j)
      exact ⟨m, c, fun _ ↦ hmc⟩
  choose e c hc using h
  exact ⟨e, c, hc⟩

end

end AlgebraicGeometry.ProjectiveSpace
