import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # Positivity on the longest cell detects real Whittaker values -/

noncomputable section

open Set TopologicalSpace MeasureTheory MeasureTheory.Measure
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open scoped Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesWhittakerUniqueness

open RealBorelTestAverage RealBorelAverageSurjectivity RealPrincipalSeriesDistribution
open RealJacquetFrobenius RealBruhatDistributionRestriction

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "W" => weylLong (r + 1) ℝ
local notation "O" => longestBruhatCell ℝ r

local instance : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
local instance : LocallyCompactSpace B := (isClosed_upperTriangularSubgroup (r + 1) ℝ).locallyCompactSpace
local instance : LocallyCompactSpace U := UpperUnipotent.locallyCompactSpace
local instance : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance : SecondCountableTopology G :=
  (show Topology.IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).isInducing.secondCountableTopology
local instance : SecondCountableTopology B :=
  (show Topology.IsInducing (Subtype.val : B → G) from Topology.IsInducing.subtypeVal).secondCountableTopology
local instance : SecondCountableTopology U :=
  (show Topology.IsInducing (Subtype.val : U → G) from Topology.IsInducing.subtypeVal).secondCountableTopology
local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩

variable (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2)
local notation "P" => principalSeries ℝ (r + 1) (posChar s e)
local notation "ds" => normalizedCharacterBlocks s e
local notation "χ" => positionBorelCharacter s e

private theorem orbitHomeomorph_apply_val (p : B × U) :
    (orbitHomeomorph p).val = (p.1.val * W * (p.2⁻¹).val).val := by
  rw [orbitHomeomorph_val]
  rfl

private theorem continuous_WhittakerCharacter_subgroup (a : ℝˣ) :
    Continuous (fun u : U => realWhittakerCharacter a u.val) :=
  (realScaledCharacter a).continuous_complex.comp (continuous_finsetSum _ fun i _ =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i.castSucc i.succ)

/-- A smooth inducing function supported in the longest cell with nonnegative phased real
part along the orbit and positive real part at the long Weyl element has nonzero value. -/
def RealWhittakerOrbitPositivityStatement : Prop :=
  ∀ (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ), RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ →
    IsWhittakerFunctional s e a ℓ → ℓ ≠ 0 → ∀ F : P,
      tsupport F.val ⊆ Units.val ⁻¹' O →
      (∀ u : U, 0 ≤ (realWhittakerCharacter a u.val * F.val (W * (u⁻¹).val)).re) →
      0 < (F.val W).re → ℓ F ≠ 0

set_option maxHeartbeats 850000 in
theorem realWhittakerOrbitPositivity : RealWhittakerOrbitPositivityStatement s e := by
  intro a ℓ hb hψ hne F hSupport hNonneg hPos
  obtain ⟨κ, Z, f, _, hκ, hκK, hAvg, hCut, hSupp⟩ := exists_averageMap_compactCutoff s e F
  have hfO : tsupport f ⊆ O := by
    intro X hX
    obtain ⟨g, hg, rfl⟩ := hSupp hX
    exact hSupport hg
  let fO : 𝓓(O, ℂ) := ⟨f, f.contDiff, f.hasCompactSupport, hfO⟩
  have hMono : (TestFunction.monoCLM ℂ fO : 𝓓(invertibleDomain r, ℂ)) = f := by
    have h : O ≤ invertibleDomain r := by rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩
    ext X
    simp [h, fO]
  obtain ⟨c, hc, hFormula⟩ := realPrincipalSeriesWhittakerOrbitFormula s e a ℓ hb hψ hne
  have h := hFormula fO
  rw [hMono, hAvg] at h
  let J (p : B × U) : ℂ := inverseWeight χ p.1 * ((modularCharacter p.1 : ℝ) : ℂ) *
    realWhittakerCharacter a p.2.val * fO (orbitHomeomorph p).val
  have hJ : Continuous J :=
    ((((continuous_inverseWeight χ (continuous_positionBorelCharacter s e)).comp continuous_fst).mul
      (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (Langlands.Haar.continuous_modularCharacter_of_locallyCompact.comp continuous_fst)))).mul
      ((continuous_WhittakerCharacter_subgroup a).comp continuous_snd)).mul
      (fO.contDiff.continuous.comp (continuous_subtype_val.comp (orbitHomeomorph (r := r)).continuous))
  have hJC : HasCompactSupport J := by
    let K : Set O := Subtype.val ⁻¹' tsupport fO
    have hK : IsCompact K := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      fO.hasCompactSupport (by simpa using fO.tsupport_subset)
    apply HasCompactSupport.of_support_subset_isCompact ((orbitHomeomorph (r := r)).isCompact_preimage.mpr hK)
    intro p hp
    by_contra hpK
    have hz : fO (orbitHomeomorph p).val = 0 := image_eq_zero_of_notMem_tsupport
      (show (orbitHomeomorph p).val ∉ tsupport fO from hpK)
    exact hp (show J p = 0 from mul_eq_zero_of_right _ hz)
  have hReal (b : B) (u : U) : (J (b, u)).re =
      ((modularCharacter b : ℝ) * κ (b.val * W * (u⁻¹).val)) *
        (realWhittakerCharacter a u.val * F.val (W * (u⁻¹).val)).re := by
    let g := W * (u⁻¹).val
    have hχ : inverseWeight χ b * (χ b : ℂ) = 1 := congrArg Units.val (inv_mul_cancel (χ b))
    change (inverseWeight χ b * ((modularCharacter b : ℝ) : ℂ) * realWhittakerCharacter a u.val *
      fO (orbitHomeomorph (b, u)).val).re = _
    rw [orbitHomeomorph_apply_val, mul_assoc b.val W, show fO (b.val * g).val = f (b.val * g).val from rfl,
      hCut, section_left_borel]
    change _ = ((modularCharacter b : ℝ) * κ (b.val * g)) * (realWhittakerCharacter a u.val * F.val g).re
    rw [← Complex.re_ofReal_mul, Complex.ofReal_mul]
    apply congrArg Complex.re
    linear_combination ((↑(modularCharacter b : ℝ) : ℂ) * realWhittakerCharacter a u.val *
      (κ (b.val * g) : ℂ) * F.val g) * hχ
  have hReNonneg (p : B × U) : 0 ≤ (J p).re := by
    obtain ⟨b, u⟩ := p
    rw [hReal]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (hκ _)) (hNonneg u)
  have hone : realWhittakerCharacter a (1 : U).val = 1 := by
    simp only [Subgroup.coe_one, realWhittakerCharacter, Units.val_one,
      Matrix.one_apply_ne Fin.castSucc_lt_succ.ne, Finset.sum_const_zero, AddChar.map_zero_eq_one]
  have hJOne : 0 < (J ((1 : B), (1 : U))).re := by
    rw [hReal, inv_one, hone, Subgroup.coe_one, Subgroup.coe_one, one_mul, mul_one, map_one,
      NNReal.coe_one, hκK W RealEqualDualConvergence.weylLong_mem_unitary, one_mul, one_mul]
    simpa only [one_mul] using hPos
  have hIntRe : 0 < ∫ p, (J p).re ∂(Measure.haar : Measure (B × U)) :=
    (Complex.continuous_re.comp hJ).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hJC.comp_left Complex.zero_re) hReNonneg hJOne.ne'
  have hIntNe : (∫ p, J p ∂(Measure.haar : Measure (B × U))) ≠ 0 := by
    intro hz
    have hi : Integrable J (Measure.haar : Measure (B × U)) := hJ.integrable_of_hasCompactSupport hJC
    have he := integral_re hi
    change (∫ p, (J p).re ∂(Measure.haar : Measure (B × U))) =
      (∫ p, J p ∂(Measure.haar : Measure (B × U))).re at he
    rw [he, hz, Complex.zero_re] at hIntRe
    exact (lt_irrefl _ hIntRe)
  intro hZero
  rw [map_smul, hZero, smul_zero] at h
  simp_rw [← orbitHomeomorph_apply_val] at h
  exact mul_ne_zero hc hIntNe h.symm

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesWhittakerUniqueness
