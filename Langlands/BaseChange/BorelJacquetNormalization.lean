import Langlands.BaseChange.RegularElementaryJacquetTraceStatement
import Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement

/-! # Normalization of the actual integral-diagonal Borel Jacquet action -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence GeneralLinear.BlockShape
open scoped BigOperators NNReal

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}

local notation "D" => F.canonicalTopologicalData
local notation "B" => singletons (r + 1)

private theorem real_zpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (q : ℝ) (hq : q ≠ 0) :
    q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, q ^ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hq, ih]

/-- The upper Borel modulus on a diagonal depends on the sum of its positive-root
order differences. -/
theorem leviModulus_singletonLevi_of_ord
    (a : Fin (r + 1) → F.Carrierˣ) (ν : Fin (r + 1) → ℤ)
    (ha : ∀ i, (D).ord (a i : F.Carrier) = ν i) :
    (((D).leviModulus B (singletonLevi F.Carrier a) : ℝ≥0) : ℝ) =
      ((D).residueCardinality : ℝ) ^ (-regularElementaryRho ν) := by
  let q := ((D).residueCardinality : ℝ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (lt_trans Nat.zero_lt_one (D).residueCardinality_gt_one).ne'
  have hAbs (i : Fin (r + 1)) : (D).normalizedAbs (a i : F.Carrier) = q ^ (-ν i) := by
    rw [(D).normalizedAbs_of_ne_zero (a i).ne_zero, ha i]
  rw [(D).leviModulus_singletonLevi]
  simp only [Units.coe_prod, NNReal.coe_prod, Units.val_div_eq_div_val, NNReal.coe_div,
    (D).normalizedAbsUnits_coe, hAbs, ← zpow_sub₀ hq]
  change (∏ i : Fin (r + 1), ∏ j ∈ Finset.univ.filter (fun j => i < j),
    q ^ (-ν i - -ν j)) = q ^ (-regularElementaryRho ν)
  rw [regularElementaryRho, ← Finset.sum_neg_distrib, real_zpow_sum _ _ _ hq]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib, real_zpow_sum _ _ _ hq]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  omega

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)

set_option quotPrecheck false in
local notation "J" => Parabolic.leviCoinvariants B (ρ.comp ((B).parabolic F.Carrier).subtype)

/-- The unnormalized action is the normalized action times the positive half-modulus
on the same Jacquet quotient. -/
theorem unnormalizedBorelJacquet_eq_half_smul (m : (B).Levi F.Carrier) (x : (B).JacquetModule ρ) :
    J m x = ((D).leviHalfModulus B m : ℂ) • (D).normalizedJacquet B ρ m x := by
  obtain ⟨v, rfl⟩ := (B).jacquetMk_surjective ρ x
  rw [(D).normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def, Units.val_inv_eq_inv_val,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  rfl

private theorem leviHalfModulus_eq_one_of_mem_integralDiagonal (m : (B).Levi F.Carrier)
    (hm : m ∈ integralDiagonalLevi F r) :
    ((D).leviHalfModulus B m : ℂ) = 1 := by
  obtain ⟨a, ha, rfl⟩ := (mem_integralDiagonalLevi_iff F m).mp hm
  have h : (D).leviModulus B (singletonLevi F.Carrier a) = 1 := by
    apply Units.ext
    apply NNReal.eq
    have hz (i : Fin (r + 1)) : (D).ord (a i : F.Carrier) = (0 : Fin (r + 1) → ℤ) i :=
      (ClassFieldTheory.Local.mem_unitSubgroup_iff_ord_eq_zero F D (a i)).mp (ha i)
    rw [leviModulus_singletonLevi_of_ord F a 0 hz]
    simp [regularElementaryRho]
  simp [h]

/-- Normalizing the Jacquet action leaves the integral-diagonal fixed subspace
unchanged inside the actual Borel Jacquet quotient. -/
def BorelJacquetNormalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)
    (V : Type v) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
    borelJacquetFixed F ρ = borelJacquetIntegralFixed F ρ

private theorem normalized_fixed_eq :
    borelJacquetFixed F ρ = borelJacquetIntegralFixed F ρ := by
  let : TopologicalSpace F.Carrier := (D).topology
  change fixedVectors J (integralDiagonalLevi F r).toSubgroup =
    fixedVectors ((D).normalizedJacquet B ρ) (integralDiagonalLevi F r).toSubgroup
  have hAct (m : (B).Levi F.Carrier) (hm : m ∈ integralDiagonalLevi F r)
      (x : (B).JacquetModule ρ) : J m x = (D).normalizedJacquet B ρ m x := by
    rw [unnormalizedBorelJacquet_eq_half_smul F ρ m x, leviHalfModulus_eq_one_of_mem_integralDiagonal F m hm,
      one_smul]
  apply le_antisymm
  · intro x hx k
    exact (hAct k k.2 x).symm.trans (hx k)
  · intro x hx k
    exact (hAct k k.2 x).trans (hx k)

theorem borelJacquetNormalization : BorelJacquetNormalizationStatement.{u, v} := by
  intro p _ K s W _ _ σ
  exact normalized_fixed_eq K σ

end Langlands.BaseChange
