import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstEndpointBounds
import Langlands.Representation.RankinSelberg.TwoBlockDominantSectionSupport
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant

/-! # Original-torus opposite support for the actual dominant product -/

noncomputable section

open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockConvergence TwoBlockLowerFixedSlice TwoBlockLowerUnipotentQuotient
  TwoBlockDominantSectionSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance originalConeTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance originalConeValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance originalConeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- On the support of the actual coefficient times the actual scalar section,
all original first-block exponents are bounded above and all original
second-block exponents are bounded below. -/
def IsTorusBlockSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (lambda : glFunctionals ψ r π) (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) (M : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    Wtest.val.val (matrix h hr (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) x y) ≠ 0 →
    scalarSection (fun i => (ell i).val) f (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) 1 ≠ 0 →
    (∀ a, lam ((succBlockShape m h).index 0 a) ≤ M) ∧
      (∀ a, -(M : ℤ) ≤ lam ((succBlockShape m h).index 1 a))

/-- Endpoint estimates and internal section-root support give one cutoff before
all original torus exponents, integral factors and rectangles. -/
theorem exists_torus_block_support
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) :
    ∃ M, IsTorusBlockSupport F h hr ψ π lambda Wtest τ ell u f M := by
  obtain ⟨B₀, _, hB₀⟩ := exists_levi_first_inverse_endpoint_bound F ψ h hr π hπ lambda Wtest
  obtain ⟨B₁, _, hB₁⟩ := exists_levi_second_endpoint_bound F ψ h hr π hπ lambda Wtest
  obtain ⟨L, hL⟩ := exists_section_torus_rootBounded F h ψ τ hτ ell u f
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨E, hE⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
    (max B₀ B₁)).exists
  refine ⟨E + (m 0 + m 1) * L, fun lam c x y hc hw hs => ?_⟩
  have hw' : Wtest.val.val (matrix h hr
      ((succBlockShape m h).leviEmbedding F.Carrier (torusLevi F h lam) * c) x y) ≠ 0 := by
    simpa only [torusLevi_embedding] using hw
  have hzero := hB₀ (torusLevi F h lam) c x y hc hw'
  have hone := hB₁ (torusLevi F h lam) c x y hc hw'
  have hzpow : F.canonicalTopologicalData.normalizedAbs
      (((torusLevi F h lam) 0)⁻¹ 0 0) =
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (lam ((succBlockShape m h).index 0 0)) := by
    change F.canonicalTopologicalData.normalizedAbs
      ((Iwasawa.torus _ _)⁻¹.val 0 0) = _
    rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_eq, ← zpow_neg,
      normalizedAbs_uniformizer_zpow F, neg_neg]
  have hopow : F.canonicalTopologicalData.normalizedAbs
      (torusLevi F h lam 1 (Fin.last (m 1)) (Fin.last (m 1))) =
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (-lam ((succBlockShape m h).index 1 (Fin.last (m 1)))) := by
    change F.canonicalTopologicalData.normalizedAbs ((Iwasawa.torus _ _).val _ _) = _
    rw [Iwasawa.torus_val, Matrix.diagonal_apply_eq, normalizedAbs_uniformizer_zpow F]
  rw [hzpow] at hzero
  rw [hopow] at hone
  have he₀ : lam ((succBlockShape m h).index 0 0) ≤ E := by
    apply (zpow_le_zpow_iff_right₀ hq).mp
    rw [zpow_natCast]
    exact hzero.trans ((le_max_left _ _).trans hE.le)
  have he₁ : -(E : ℤ) ≤ lam ((succBlockShape m h).index 1 (Fin.last (m 1))) := by
    have he : -lam ((succBlockShape m h).index 1 (Fin.last (m 1))) ≤ E := by
      apply (zpow_le_zpow_iff_right₀ hq).mp
      rw [zpow_natCast]
      exact hone.trans ((le_max_right _ _).trans hE.le)
    omega
  have hroots := hL lam c hc hs
  constructor
  · intro a
    have hp := (hroots 0).le_of_le (Fin.zero_le a)
    push_cast
    push_cast at hp
    have hn : (0 : ℤ) ≤ m 1 * L := by positivity
    nlinarith
  · intro a
    have hp := (hroots 1).le_of_le (Fin.le_last a)
    push_cast
    push_cast at hp
    have hn : (0 : ℤ) ≤ m 0 * L := by positivity
    nlinarith

/-- Original block cutoffs give the standard opposing cone after block rotation. -/
theorem oppositeCone_rotated_of_block_bounds
    (lam : Fin (t + 1) → ℤ) (M : ℕ) (a : Fin t) (ha : a.val = m 1)
    (h₀ : ∀ b, rotatedExponents h lam ((succBlockShape m h).index 0 b) ≤ M)
    (h₁ : ∀ b, -(M : ℤ) ≤ rotatedExponents h lam ((succBlockShape m h).index 1 b)) :
    OppositeCone M (Finset.Iic a.castSucc) lam := by
  classical
  constructor
  · intro i hi
    have hi' : i.val ≤ m 1 := by
      have := Finset.mem_Iic.mp hi
      change i.val ≤ a.val at this
      omega
    let b : Fin (m 1 + 1) := ⟨i.val, by omega⟩
    have he : (succBlockShape m h).reversePermutation.symm
        ((succBlockShape m h).index 1 b) = i := by
      apply Fin.ext
      exact val_reversePermutation_symm_index_one h b
    simpa only [rotatedExponents, he] using h₁ b
  · intro i hi
    have hi' : m 1 + 1 ≤ i.val := by
      have : ¬i.val ≤ a.val := fun hle => hi (Finset.mem_Iic.mpr hle)
      omega
    have hsum : m 0 + 1 + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    let b : Fin (m 0 + 1) := ⟨i.val - (m 1 + 1), by have := i.isLt; omega⟩
    have he : (succBlockShape m h).reversePermutation.symm
        ((succBlockShape m h).index 0 b) = i := by
      apply Fin.ext
      rw [val_reversePermutation_symm_index_zero]
      dsimp only [b]
      omega
    simpa only [rotatedExponents, he] using h₀ b

/-- At actual inverse-rotated torus representatives, simultaneous nonvanishing
of the ambient coefficient and scalar section forces one opposite cone. -/
theorem exists_rotated_torus_oppositeCone
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ M : ℕ, ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
      (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
      c ∈ integralOpen F t →
      let g := (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c
      Wtest.val.val (matrix h hr g x y) ≠ 0 →
      scalarSection (fun i => (ell i).val) f g 1 ≠ 0 →
      OppositeCone M (Finset.Iic a.castSucc) lam := by
  obtain ⟨M, hM⟩ := exists_torus_block_support F h hr ψ π hπ lambda Wtest τ hτ ell u f
  refine ⟨M, fun lam c x y hc hw hs => ?_⟩
  have he : (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c =
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        (rotatedExponents h lam) * ((blockRotation h F.Carrier)⁻¹ * c) := by
    rw [blockRotation_inv_mul_torus, mul_assoc]
  rw [he] at hw hs
  obtain ⟨h₀, h₁⟩ := hM (rotatedExponents h lam) ((blockRotation h F.Carrier)⁻¹ * c)
    x y (blockRotation_inv_mul_mem_integralOpen F h hc) hw hs
  exact oppositeCone_rotated_of_block_bounds h lam M a ha h₀ h₁

end Langlands.RankinSelberg.TwoBlockDominantRectangular
