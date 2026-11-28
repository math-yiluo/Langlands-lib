import Langlands.Geometry.Building.TorusFiltration.PositiveUnipotentProof
import Langlands.GroupScheme.Rational.UnipotentPointsExponent

/-! # Coprime powering on positive minimal congruent terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 180000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "κ" => IsLocalRing.ResidueField O
local notation "p" => ringChar κ
local notation "P" => minimalCongruentPoints F T hT

set_option maxHeartbeats 1300000 in
private theorem exists_pPower_mem_of_mem_plus {x : rationalPoints T.toGrp}
    (hx : x ∈ minimalCongruentPlus F T hT 0) (r : ℝ≥0) :
    ∃ n : ℕ, x ^ (p ^ n) ∈ P r := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  let a := min (s : ℝ≥0) (1 / 2)
  have ha : 0 < a := lt_min s.property (by norm_num)
  have ha₁ : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let q : Set.Iio (1 : ℝ≥0) := ⟨a, ha₁⟩
  have hq : x ∈ P q := minimalCongruentPoints_antitone F T hT (min_le_left _ _) hs
  let N := minimalCongruentModel F T hT q
  have hN : N.val.IsSmooth := N.property.1
  have hNpts := N.property.2.2
  obtain ⟨y, hy⟩ := hNpts.ge hq
  let : Smooth N.val.group.X.hom := hN
  let : Algebra 𝓀[F] κ := (residueToFixedField F).toAlgebra
  let : Fact (Nat.Prime p) := ⟨by rw [← Algebra.ringChar_eq 𝓀[F] κ]; exact CharP.prime_ringChar 𝓀[F]⟩
  have hUni := minimalCongruentPositiveUnipotent F T hT q N.val ha hN hNpts
  obtain ⟨d, hd⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hUni
  have hy₁ : y ^ (p ^ d) ∈ N.val.congruenceKernelAt 1 := by
    rw [N.val.congruenceKernelAt_one, N.val.mem_congruenceKernel, map_pow, hd _ _]
  let j := ⌈r⌉₊
  let k : ℕ+ := ⟨((1 : ℕ+) : ℕ) + j, Nat.add_pos_left (1 : ℕ+).pos j⟩
  have hk : (y ^ (p ^ d)) ^ (p ^ j) ∈ N.val.congruenceKernelAt k :=
    N.val.pow_pow_mem_congruenceKernelAt 1 p (IntegralModel.residueChar_mem_maximalIdeal (R := O)) hy₁ j
  have hPower : x ^ (p ^ (d + j)) ∈ N.val.congruenceSubgroupAt k := by
    refine ⟨_, hk, ?_⟩
    rw [map_pow, map_pow, hy, pow_add, pow_mul]
  have hrk : r ≤ (q : ℝ≥0) + (k : ℕ) := by
    have hkj : ⌈r⌉₊ ≤ (k : ℕ) := Nat.le_add_left _ _
    exact ((Nat.le_ceil r).trans (by exact_mod_cast hkj)).trans (le_add_of_nonneg_left zero_le)
  have hShift := minimalCongruentPoints_add_pnat F T hT q k N.val hN
    (hNpts.trans (minimalCongruentPoints_of_lt_one F T hT q))
  exact ⟨d + j, minimalCongruentPoints_antitone F T hT hrk (hShift.ge hPower)⟩

set_option maxHeartbeats 750000 in
/-- Within the positive union, belonging to a fixed minimal congruent depth
can be checked after raising to an exponent prime to the residue characteristic. -/
theorem minimalCongruentPoints_mem_of_coprime_pow {x : rationalPoints T.toGrp}
    (hx : x ∈ minimalCongruentPlus F T hT 0) (r : ℝ≥0)
    {m : ℕ} (hm : m.Coprime p) (hxm : x ^ m ∈ P r) : x ∈ P r := by
  obtain ⟨n, hxn⟩ := exists_pPower_mem_of_mem_plus F T hT hx r
  have hc : IsCoprime (m : ℤ) ((p ^ n : ℕ) : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hm.pow_right n)
  obtain ⟨a, b, hab⟩ := hc
  have h : x ^ (a * (m : ℤ) + b * ((p ^ n : ℕ) : ℤ)) ∈ P r := by
    rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact (P r).mul_mem ((P r).zpow_mem hxm a) ((P r).zpow_mem hxn b)
  rwa [hab, zpow_one] at h

end Langlands.Geometry.Building
