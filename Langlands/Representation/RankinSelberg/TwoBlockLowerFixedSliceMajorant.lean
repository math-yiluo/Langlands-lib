import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSummability
import Langlands.Representation.RankinSelberg.TwoBlockLowerCompactFourier
import Langlands.Representation.RankinSelberg.TwoBlockLowerIntegralRotation

/-! # A concrete cone majorant for the Section 4.7 lower integrand -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockConvergence TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Moving the inverse block rotation through the canonical torus permutes its
integer exponents. -/
theorem blockRotation_inv_mul_torus (lam : Fin (t + 1) → ℤ) :
    (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam =
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        (rotatedExponents h lam) * (blockRotation h F.Carrier)⁻¹ :=
  blockRotation_inv_mul_diagonal h _

/-- Section growth in the rotated coordinates, with the exact opposing twist
and all remaining diagonal growth absorbed into a single fixed base. -/
theorem exists_rotated_section_growth (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Fin (t + 1) → ℤ)
        (k : GeneralLinear (t + 1) F.Carrier), k ∈ integralOpen F t →
        ‖scalarSection
          (fun i => (twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)).val) f
          ((blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * k) 1‖ ≤
          C * B ^ torusSize lam *
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
  obtain ⟨B, hB, hgrowth⟩ := exists_section_growth F h ψ τ hτ ell
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  let D : ℝ := q ^ ((m 0 + 1) * (m 1 + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  refine ⟨B * D, one_le_mul_of_one_le_of_one_le hB hD, fun u f => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth u f
  refine ⟨C, hC0, fun lam k hk => ?_⟩
  have hb := hC ((blockRotation h F.Carrier)⁻¹ * k)
    (blockRotation_inv_mul_mem_integralOpen F h hk)
    (torusSize (rotatedExponents h lam)) (torusLevi F h (rotatedExponents h lam))
    (torusLevi_entryBounded F h (rotatedExponents h lam))
  rw [torusLevi_embedding, torusSize_rotatedExponents,
    torusLevi_rotated_twist h F lam j hj u] at hb
  have heq : (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * k =
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        (rotatedExponents h lam) * ((blockRotation h F.Carrier)⁻¹ * k) := by
    rw [blockRotation_inv_mul_torus, mul_assoc]
  rw [heq]
  have hm := torusLevi_inv_halfModulus_le F h (rotatedExponents h lam)
  rw [torusSize_rotatedExponents] at hm
  calc
    _ ≤ C * B ^ torusSize lam *
        ‖((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h)
          (torusLevi F h (rotatedExponents h lam)) : ℂˣ) : ℂ)⁻¹‖ *
        q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := hb
    _ ≤ C * B ^ torusSize lam * D ^ torusSize lam *
        q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- Exact representative formula for the integrand transported to the standard
quotient. The test coefficient is evaluated without a left rotation. -/
theorem integrand_standard_mk (ψ : UnitaryAdditiveCharacter F.Carrier)
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
    (Wtest : WhittakerFunctions ψ t) (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (μ : AdditiveHaarMeasure F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ell f Wtest Φ μ
        ((lowerToStandard h F.Carrier).symm (Quotient.mk _ g)) =
      Wtest.val g * scalarSection (fun i => (ell i).val) f
        ((blockRotation h F.Carrier)⁻¹ * g) 1 *
      partialSection h ψ μ Φ ((blockRotation h F.Carrier)⁻¹ * g) := by
  rw [lowerToStandard_symm_mk, integrand_mk, mul_inv_cancel_left]

/-- One fixed growth base works for every later section, coefficient and row
Schwartz function. Nonzero values are confined to an opposing cone. -/
theorem exists_integrand_torus_majorant (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (lambda : glFunctionals ψ t π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
      ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
        ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F.Carrier),
          k ∈ integralOpen F t →
          let z := (lowerToStandard h F.Carrier).symm (Quotient.mk _
            (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
              F.canonicalTopologicalData) lam * k))
          let E := integrand
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
            f Wtest.val Φ ν.val
          ‖E z‖ ≤ C * B ^ torusSize lam *
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) ∧
          (E z ≠ 0 → OppositeCone M (Finset.Iic j.castSucc) lam) := by
  obtain ⟨Bs, hBs, hsection⟩ := exists_rotated_section_growth F h ψ τ hτ ell j hj
  obtain ⟨Bw, hBw, hcoeff⟩ := exists_coefficient_torusSize_growth F ψ π hπ lambda
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  refine ⟨Bw * Bs * q,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hBw hBs) hq.le,
    fun u f Wtest Φ => ?_⟩
  obtain ⟨Cs, hCs0, hCs⟩ := hsection u f
  obtain ⟨Cw, hCw0, hCw⟩ := hcoeff Wtest 1
  obtain ⟨L, hL⟩ := exists_coefficient_rootBounded F ψ π hπ.1.1 lambda Wtest
  obtain ⟨Cf, M, hCf0, hCf⟩ :=
    exists_partialSection_rotated_torus_compact_bounds h ψ ν.val Φ ν.property
      (integralOpen F t) (isCompact_integralOpen F t) j hj
  refine ⟨Cw * Cs * Cf, M + t * L, by positivity, fun lam k hk => ?_⟩
  dsimp only
  rw [integrand_standard_mk]
  simp only [← mul_assoc]
  have hs := hCs lam k hk
  have hw := hCw lam k hk
  simp only [one_mul] at hw
  have hf := hCf lam k hk
  constructor
  · rw [norm_mul, norm_mul]
    calc
      _ ≤ (Cw * Bw ^ torusSize lam) *
          (Cs * Bs ^ torusSize lam * q ^
            (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ))) *
          (Cf * q ^ torusSize lam) := by
        exact mul_le_mul
          (mul_le_mul hw hs (norm_nonneg _) (by positivity)) hf.1
          (norm_nonneg _) (by positivity)
      _ = _ := by simp only [mul_pow]; ring
  · intro hne
    have hwne := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
    have hfne := (mul_ne_zero_iff.mp hne).2
    obtain ⟨hhi, hlo⟩ := hf.2 hfne
    exact oppositeCone_of_endpoints (hL lam k hk hwne) j hlo hhi

/-- A nonnegative bound supported on the opposing cone. -/
def coneMajorant {n : ℕ} (s : Finset (Fin n)) (C B q u : ℝ) (M : ℕ)
    (lam : Fin n → ℤ) : ℝ :=
  if OppositeCone M s lam then
    C * B ^ torusSize lam * q ^ (-u * (twistDegree s lam : ℝ)) else 0

theorem coneMajorant_nonneg {n M : ℕ} (s : Finset (Fin n))
    {C B q u : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : 0 ≤ q) (lam : Fin n → ℤ) :
    0 ≤ coneMajorant s C B q u M lam := by
  unfold coneMajorant
  split_ifs <;> positivity

theorem diagonalDensity_nonneg {n : ℕ} (lam : Fin n → ℤ) :
    0 ≤ diagonalDensity F lam :=
  inv_nonneg.mpr (Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg
    (fun _ _ => F.canonicalTopologicalData.normalizedAbs_nonneg _)))

/-- A single real threshold, before all later analytic inputs, yields a uniform
compact bound whose product with the exact Iwasawa density is summable. -/
theorem exists_summable_integrand_majorant (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (lambda : glFunctionals ψ t π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ C : ℝ, ∀ (u : ℝ), C < u →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (Wtest : (coefficientModel π lambda).toSubmodule)
        (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
      ∃ A : (Fin (t + 1) → ℤ) → ℝ,
        (∀ lam, 0 ≤ A lam) ∧
        Summable (fun lam => diagonalDensity F lam * A lam) ∧
        ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F.Carrier),
          k ∈ integralOpen F t →
          ‖integrand
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
            f Wtest.val Φ ν.val
            ((lowerToStandard h F.Carrier).symm (Quotient.mk _
              (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
                F.canonicalTopologicalData) lam * k)))‖ ≤ A lam := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_integrand_torus_majorant F h ψ ν π hπ lambda τ hτ ell j hj
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  let D : ℝ := q ^ (2 * (t + 1) * (t + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨C, _, hC⟩ := exists_geometric_twist_threshold (B := D * B) hq
  refine ⟨C, fun u hu f Wtest Φ => ?_⟩
  obtain ⟨hu0, hr⟩ := hC u hu
  obtain ⟨K, M, hK0, hK⟩ := hbound u f Wtest Φ
  refine ⟨coneMajorant (Finset.Iic j.castSucc) K B q u M,
    coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le), ?_, ?_⟩
  · apply Summable.of_nonneg_of_le
      (fun lam => mul_nonneg (diagonalDensity_nonneg F lam)
        (coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le) lam)) _
      ((summable_cone_twist (M := M) (Finset.Iic j.castSucc) hq
        (mul_nonneg (zero_le_one.trans hD) hB0) hu0 hr).mul_left K)
    intro lam
    unfold coneMajorant
    split_ifs with hc
    · calc
        _ ≤ D ^ torusSize lam * (K * B ^ torusSize lam *
            q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ))) :=
          mul_le_mul_of_nonneg_right (diagonalDensity_le F lam) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · simp
  · intro lam k hk
    obtain ⟨hb, hs⟩ := hK lam k hk
    unfold coneMajorant
    split_ifs with hc
    · exact hb
    · have hz : integrand
          (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
          f Wtest.val Φ ν.val
          ((lowerToStandard h F.Carrier).symm (Quotient.mk _
            (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
              F.canonicalTopologicalData) lam * k))) = 0 := by
        by_contra he
        exact hc (hs he)
      rw [hz, norm_zero]

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
