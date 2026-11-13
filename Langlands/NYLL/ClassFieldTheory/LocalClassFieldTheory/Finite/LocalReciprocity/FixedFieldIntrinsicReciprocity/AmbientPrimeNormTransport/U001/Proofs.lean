/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Prove the published closed form of M283.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709 under the source theorem name with
the Langlands.NYLL namespace prefix. The original proof, which uses the
inverse of a chosen uniformizer and transports its irreducibility through the
induced equivalence of valuation rings, is replaced by a new proof from
Mathlib only: the two normalized valuations have the same nonpositive part,
hence the same kernel, and both take the value one. Three helper lemmas about
the published valuationMap are added. Import only the published M283.001
Statements module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
Worker 216, 13 November 2026: reuse Worker 56's shared proof draft unchanged;
check its correspondence and revise its paired proof documentation.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U001.Statements

/-!
# Valuation-one units under valuation-compatible ring equivalences: proof

The proof of the published closed assertion that a ring equivalence between
nonarchimedean local fields matching their valuation subrings carries some
unit of normalized valuation one to a unit of normalized valuation one.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

/-- The normalized valuation of a unit, viewed in `ℤᵐ⁰`, is the image of its
valuation under Mathlib's order isomorphism of the value group with `ℤᵐ⁰`. -/
theorem coe_valuationUnitsMulHom_eq
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    ((IsNonarchimedeanLocalField.valuationUnitsMulHom K x : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K (x : K)) := by
  simp [IsNonarchimedeanLocalField.valuationUnitsMulHom]

/-- A unit has nonpositive normalized valuation exactly when it lies in the
valuation subring. -/
theorem valuationMap_nonpos_iff
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) ≤ 0 ↔
      (x : K) ∈ (ValuativeRel.valuation K).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff]
  change Multiplicative.toAdd (IsNonarchimedeanLocalField.valuationUnitsMulHom K x) ≤
      Multiplicative.toAdd (1 : Multiplicative ℤ) ↔ _
  rw [Multiplicative.toAdd_le, ← WithZero.coe_le_coe, coe_valuationUnitsMulHom_eq,
    WithZero.coe_one,
    ← map_one (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K),
    map_le_map_iff]

/-- Some unit has normalized valuation one. -/
theorem exists_valuationMap_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ x : Kˣ, IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) = 1 := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
    ((_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h := congrArg (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) hy
    simp at h
  refine ⟨Units.mk0 y hy0, ?_⟩
  have h := coe_valuationUnitsMulHom_eq K (Units.mk0 y hy0)
  rw [Units.val_mk0, hy, OrderMonoidIso.apply_symm_apply, WithZero.coe_inj] at h
  change Multiplicative.toAdd
    (IsNonarchimedeanLocalField.valuationUnitsMulHom K (Units.mk0 y hy0)) = 1
  rw [h, toAdd_ofAdd]

/-- A valuation-subring-preserving ring equivalence carries some unit of
valuation one to a unit of valuation one. -/
theorem exists_valuationOne_unit_of_ringEquiv :
    exists_valuationOne_unit_of_ringEquivStatement := by
  intro L M _ _ _ _ _ _ _ _ phi hmem
  let F : Additive Lˣ →+ ℤ := IsNonarchimedeanLocalField.valuationMap L
  let G : Additive Lˣ →+ ℤ :=
    (IsNonarchimedeanLocalField.valuationMap M).comp
      (MulEquiv.toAdditive (Units.mapEquiv phi.toMulEquiv)).toAddMonoidHom
  have hG : ∀ x : Lˣ, G (Additive.ofMul x) =
      IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul (Units.mapEquiv phi.toMulEquiv x)) := fun _ => rfl
  have hle : ∀ a : Additive Lˣ, F a ≤ 0 ↔ G a ≤ 0 := by
    intro a
    obtain ⟨x, rfl⟩ : ∃ x : Lˣ, Additive.ofMul x = a := ⟨a.toMul, ofMul_toMul a⟩
    rw [hG]
    change IsNonarchimedeanLocalField.valuationMap L (Additive.ofMul x) ≤ 0 ↔ _
    rw [valuationMap_nonpos_iff, valuationMap_nonpos_iff, Units.coe_mapEquiv]
    exact hmem x
  have h0 : ∀ a : Additive Lˣ, F a = 0 → G a = 0 := by
    intro a ha
    have h1 : G a ≤ 0 := (hle a).1 ha.le
    have h2 : G (-a) ≤ 0 := (hle (-a)).1 (by rw [map_neg, ha, neg_zero])
    rw [map_neg] at h2
    omega
  obtain ⟨p, hp⟩ := exists_valuationMap_eq_one L
  obtain ⟨q', hq'⟩ := exists_valuationMap_eq_one M
  let q : Lˣ := (Units.mapEquiv phi.toMulEquiv).symm q'
  have hFp : F (Additive.ofMul p) = 1 := hp
  have hGq : G (Additive.ofMul q) = 1 := by
    rw [hG, MulEquiv.apply_symm_apply]
    exact hq'
  have hGp : 0 < G (Additive.ofMul p) := by
    by_contra hcon
    have := (hle (Additive.ofMul p)).2 (not_lt.mp hcon)
    omega
  have hkey := h0 (Additive.ofMul q - F (Additive.ofMul q) • Additive.ofMul p) (by
    rw [map_sub, map_zsmul, hFp, smul_eq_mul, mul_one, sub_self])
  rw [map_sub, map_zsmul, hGq, smul_eq_mul, sub_eq_zero] at hkey
  have hGp1 : G (Additive.ofMul p) = 1 :=
    Int.eq_one_of_mul_eq_one_left hGp.le hkey.symm
  exact ⟨p, hp, hGp1⟩

end Langlands.NYLL.LocalClassFieldTheory
