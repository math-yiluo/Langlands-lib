import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestStatement
/-!
# Compact mirabolic unit tests for every unequal-rank JPSS block: proof

One positive principal congruence level `a` is used in both ranks. The larger
test is the coset extension of the standard character from the level-`a`
principal congruence subgroup of the mirabolic group. A Schur-complement
computation shows that the block matrix `diag(g, I) (1 + X)` lies in its
support exactly when `g` lies in `N K(a)` and the rectangular entries lie in
`𝔪^a`. A rescaled actual coefficient function of a vector fixed by `K(a)`
then makes the integrand a constant multiple of the indicator of a compact
open quotient orbit times a compact open rectangle.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicUnitTest
open Langlands.AllField.RankinSelberg

open MeasureTheory Topology
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding ModelKirillovTransferStatement
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uW

namespace UnequalRankMirabolicUnitTest
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest
open Langlands.AllField.RankinSelberg.UnequalRankMirabolicUnitTest
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicUnitTest
open Langlands.AllField.RankinSelberg

section Algebra

variable {F : Type uF} [Field F] [ValuativeRel F]

end Algebra

section Blocks

variable {F : Type uF} [Field F] [ValuativeRel F] {n j k a : ℕ}

end Blocks

section Measure

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]

end Measure

section Rectangular

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

end Rectangular

end UnequalRankMirabolicUnitTest

open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest in
open Langlands.AllField.RankinSelberg.UnequalRankMirabolicUnitTest in
/-- Every unequal-rank JPSS block admits a compact mirabolic test function and
an actual smaller coefficient-model vector whose product integral converges and
equals one for every complex parameter. -/
theorem unequalRankMirabolicUnitTest (F : Type uF) [Field F]
    (T : LocalFieldData F) (n j k : ℕ) :
    UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace F := borel _
  have : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  have : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  have : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  have : SigmaCompactSpace F := T.sigmaCompactSpace
  intro ψ _ μ hμ ν W _ _ σ hσ ℓ' hℓ'
  -- A vector with nonzero functional value and an open subgroup fixing it.
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hℓ'
  rw [LinearMap.zero_apply] at hw
  obtain ⟨Kw, hKw⟩ := hσ.1.1 w
  have hfix : ∀ g ∈ Kw, σ g w = w := fun g hg =>
    (Representation.mem_invariants _ w).1 hKw ⟨g, hg⟩
  -- A level for the smaller rank: inside `Kw` and the determinant-norm kernel.
  have hU₁ : (Kw : Set (Langlands.GeneralLinear (n + 1) F)) ∩
      ((T.determinantNorm (n + 1)).ker : Set (Langlands.GeneralLinear (n + 1) F)) ∈
        𝓝 (1 : Langlands.GeneralLinear (n + 1) F) :=
    Filter.inter_mem (Kw.isOpen.mem_nhds Kw.one_mem)
      ((T.isOpen_ker_determinantNorm (n + 1)).mem_nhds (one_mem _))
  obtain ⟨a₁, ha₁, hK₁⟩ :=
    Conductor.exists_pos_principalLevelOpenSubgroup_subset F n hU₁
  -- A level for the larger rank: inside the kernel of the standard character.
  have hker : IsOpen ((standardCharacter ψ (n + (j + k + 1))).ker :
      Set (upperUnipotent (n + (j + k + 1) + 1) F)) := by
    let := T.upperUnipotentNonarchimedean (n + (j + k + 1) + 1)
    exact isOpen_ker_of_continuous_complex_character _
      (standardCharacterContinuous ψ (n + (j + k + 1))).continuous
  have hN₁ := hker.mem_nhds (standardCharacter ψ (n + (j + k + 1))).ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hN₁
  obtain ⟨O, hO, hOK⟩ := hN₁
  obtain ⟨a₂, -, hK₂⟩ :=
    Conductor.exists_pos_principalLevelOpenSubgroup_subset F (n + (j + k + 1)) hO
  obtain ⟨a, ha₁a, ha₂a, ha⟩ : ∃ a, a₁ ≤ a ∧ a₂ ≤ a ∧ 0 < a :=
    ⟨max a₁ a₂, le_max_left _ _, le_max_right _ _, lt_max_of_lt_left ha₁⟩
  have hKt : ∀ c ∈ Conductor.principalLevelSubgroup F n a,
      c ∈ Kw ∧ T.determinantNorm (n + 1) c = 1 := by
    intro c hc
    have h := hK₁ (Conductor.principalLevelSubgroup_antitone F n ha₁a hc)
    exact ⟨h.1, MonoidHom.mem_ker.mp h.2⟩
  -- The larger test: the standard character on `N`-cosets of `H`, extended by zero.
  let H : Subgroup (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) :=
    Conductor.principalLevelSubgroup F (n + (j + k + 1)) a ⊓
      GeneralLinear.mirabolic (n + (j + k + 1)) F
  have hθ : ∀ u : upperUnipotent (n + (j + k + 1) + 1) F,
      (u : Langlands.GeneralLinear (n + (j + k + 1) + 1) F) ∈ H →
        standardCharacter ψ (n + (j + k + 1)) u = 1 := by
    intro u hu
    have h₁ : (u : Langlands.GeneralLinear (n + (j + k + 1) + 1) F) ∈ O :=
      hK₂ (Conductor.principalLevelSubgroup_antitone F _ ha₂a (Subgroup.mem_inf.mp hu).1)
    have h₂ : u ∈ Subtype.val ⁻¹' O := h₁
    exact MonoidHom.mem_ker.mp (hOK h₂)
  let φ : WhittakerFunctions ψ (n + (j + k + 1)) :=
    ⟨MirabolicUnitTest.cosetExtension _ H (standardCharacter ψ (n + (j + k + 1))),
      fun u g => MirabolicUnitTest.cosetExtension_left hθ u g⟩
  let Kr : Subgroup (GeneralLinear.mirabolic (n + (j + k + 1)) F) :=
    (Conductor.principalLevelSubgroup F (n + (j + k + 1)) a).comap
      (GeneralLinear.mirabolic (n + (j + k + 1)) F).subtype
  have hH : ∀ m : Kr, m.val.val ∈ H := fun m =>
    Subgroup.mem_inf.mpr ⟨m.property, m.val.property⟩
  have hφ : IsMirabolicTestFunction ψ (n + (j + k + 1)) φ := by
    refine isMirabolicTestFunction_of_compact_mirabolic_support ψ φ Kr ?_
      (Conductor.principalLevelOpenSubgroup F (n + (j + k + 1)) a) ?_ ?_ ?_
    · exact (GeneralLinear.Mirabolic.isClosed (F := F)
        (n := n + (j + k + 1))).isClosedEmbedding_subtypeVal.isCompact_preimage
        (Conductor.isCompact_principalLevelOpenSubgroup F _ a)
    · intro g hg hP
      exact ⟨⟨g, hP⟩, hg, rfl⟩
    · intro g hg
      apply MirabolicUnitTest.cosetExtension_eq_zero
      rintro ⟨u, h, hh, rfl⟩
      exact hg ⟨u, ⟨⟨h, (Subgroup.mem_inf.mp hh).2⟩, (Subgroup.mem_inf.mp hh).1⟩, rfl⟩
    · intro g m
      exact MirabolicUnitTest.cosetExtension_right hθ g (hH m)
  -- The support sets, their masses and the rescaling constant.
  let Ω : Set (LeftUnipotentQuotient n F) :=
    compactOpenQuotientOrbit (upperUnipotent (n + 1) F)
      (Conductor.principalLevelOpenSubgroup F n a)
  let X : Set (Matrix (Fin j) (Fin (n + 1)) F) :=
    {x | ∀ p l, x p l ∈ levelSet F a}
  obtain ⟨hΩpos, hΩfin⟩ := hμ.compactOpenQuotientOrbit_mass
    (Conductor.principalLevelOpenSubgroup F n a)
    (Conductor.isCompact_principalLevelOpenSubgroup F n a)
  have hSpos : 0 < ν.measure (levelSet F a) :=
    (isOpen_levelSet a).measure_pos _ ⟨0, zero_mem_levelSet a⟩
  have hSfin : ν.measure (levelSet F a) < ⊤ := (isCompact_levelSet a).measure_lt_top
  have hXeq := rectangularMeasure_entries ν j (n + 1) (levelSet F a)
  have hXpos : 0 < rectangularMeasure ν j (n + 1) X := by
    rw [hXeq]
    exact ENNReal.pow_pos (ENNReal.pow_pos hSpos _) _
  have hXfin : rectangularMeasure ν j (n + 1) X < ⊤ := by
    rw [hXeq]
    exact ENNReal.pow_lt_top (ENNReal.pow_lt_top hSfin)
  have hΩmeas : MeasurableSet Ω := (isOpen_compactOpenQuotientOrbit _ _).measurableSet
  have hXmeas : MeasurableSet X := measurableSet_entries (isOpen_levelSet a).measurableSet
  have hΩ0 : μ.real Ω ≠ 0 := (ENNReal.toReal_pos hΩpos.ne' hΩfin.ne).ne'
  have hX0 : (rectangularMeasure ν j (n + 1)).real X ≠ 0 :=
    (ENNReal.toReal_pos hXpos.ne' hXfin.ne).ne'
  let C : ℂ := ((μ.real Ω * (rectangularMeasure ν j (n + 1)).real X : ℝ) : ℂ)⁻¹
  -- The rescaled actual coefficient vector, constant `C` on the smaller level.
  let f' : (coefficientModel σ ℓ').toSubmodule := (C * (ℓ'.val w)⁻¹) • modelMap σ ℓ' w
  have hf' : ∀ c ∈ Conductor.principalLevelSubgroup F n a, f'.val.val c = C := by
    intro c hc
    change (C * (ℓ'.val w)⁻¹) * ℓ'.val (σ c w) = C
    rw [hfix c (hKt c hc).1, mul_assoc, inv_mul_cancel₀ hw, mul_one]
  have hweight : ∀ c ∈ Conductor.principalLevelSubgroup F n a, ∀ z : ℂ,
      determinantWeight (normalizedAbsoluteValue T) c z = 1 := by
    intro c hc z
    have h := T.determinantNorm_coe (n + 1) c
    rw [(hKt c hc).2, Units.val_one, NNReal.coe_one] at h
    have h' : T.normalizedAbs (Matrix.det c.val) = 1 := h.symm
    change ((T.normalizedAbs (Matrix.det c.val) : ℝ) : ℂ) ^ z = 1
    rw [h', Complex.ofReal_one, Complex.one_cpow]
  -- The integrand is `C` times the indicator of `Ω × X`.
  have hval : ∀ (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
      (q : LeftUnipotentQuotient n F),
      unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ f'.val s x q =
        (Ω ×ˢ X).indicator (fun _ => C) (q, x) := by
    intro s x q
    induction q using Quotient.inductionOn with
    | h g =>
      by_cases hgx : (Quotient.mk _ g, x) ∈ Ω ×ˢ X
      · rw [Set.indicator_of_mem hgx]
        obtain ⟨⟨c, hc, hcg⟩, hx⟩ := hgx
        dsimp only at hcg
        rw [← hcg, leftQuotientMap_apply, unequalRankIntegrand_mk]
        have hM : unequalRankMatrix j k c x ∈ H := unequalRankMatrix_mem ha hc hx
        have h1 : φ.val (unequalRankMatrix j k c x) = 1 := by
          simpa using MirabolicUnitTest.cosetExtension_mul hθ 1 hM
        rw [h1, hf' c hc, hweight c hc, one_mul, mul_one]
      · rw [Set.indicator_of_notMem hgx, unequalRankIntegrand_mk]
        have hz : φ.val (unequalRankMatrix j k g x) = 0 := by
          apply MirabolicUnitTest.cosetExtension_eq_zero
          rintro ⟨u, h, hh, hgxu⟩
          obtain ⟨⟨c, hc, hgc⟩, hx⟩ :=
            exists_of_unequalRankMatrix_eq ha u (Subgroup.mem_inf.mp hh).1 hgxu
          exact hgx ⟨⟨c, hc, Quotient.sound (QuotientGroup.rightRel_apply.mpr hgc)⟩, hx⟩
        rw [hz, zero_mul, zero_mul]
  refine ⟨φ, f', hφ, fun s => ⟨?_, ?_⟩⟩
  · -- Integrability of a constant on a product of finite-measure sets.
    have hint : Integrable ((Ω ×ˢ X).indicator fun _ => C)
        (μ.prod (rectangularMeasure ν j (n + 1))) := by
      rw [integrable_indicator_iff (hΩmeas.prod hXmeas)]
      exact integrableOn_const
        ((Measure.prod_prod_le _ _).trans_lt (ENNReal.mul_lt_top hΩfin hXfin)).ne
    exact hint.congr (Filter.Eventually.of_forall fun qx => (hval s qx.2 qx.1).symm)
  · -- The inner integral over `X`, then the outer integral over `Ω`.
    have hinner : ∀ q, ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ
        f'.val s x q ∂(rectangularMeasure ν j (n + 1)) =
          Ω.indicator (fun _ => (rectangularMeasure ν j (n + 1)).real X • C) q := by
      intro q
      by_cases hq : q ∈ Ω
      · rw [Set.indicator_of_mem hq, ← integral_indicator_const C hXmeas]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change _ = X.indicator (fun _ => C) x
        refine (hval s x q).trans ?_
        by_cases hx : x ∈ X
        · rw [Set.indicator_of_mem (Set.mk_mem_prod hq hx), Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem hx]
      · rw [Set.indicator_of_notMem hq]
        have h0 : ∀ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ
            f'.val s x q = 0 := fun x => by
          rw [hval s x q, Set.indicator_of_notMem (fun h => hq h.1)]
        simp only [h0, integral_zero]
    unfold unequalRankIntegral
    simp only [hinner]
    rw [integral_indicator_const _ hΩmeas, Complex.real_smul, Complex.real_smul,
      ← mul_assoc, ← Complex.ofReal_mul]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (mul_ne_zero hΩ0 hX0))

end Langlands.AllField.RankinSelberg
