import Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof
import Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-!
# Proof of the same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)

The cutoff set is a principal-unit neighborhood of `1`, small enough that the
quasicharacter is trivial on it, that it lies in the given open set, and that
the scalar diagonal matrices it defines fix a vector representing `f₂`.
The proof follows the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionScalarCutoffStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionScalarCutoff rankOneExtensionWhittakerContraction rankOneWhittakerType zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open scoped WithZero
open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

namespace ScalarCutoffProof
open Langlands.RankinSelberg.ScalarCutoffProof hiding cutoffSet cutoffSet_isCompact_isClosed cutoffSet_isOpen exists_unit_of_mem_cutoffSet mem_cutoffSet_iff one_mem_cutoffSet zero_not_mem_cutoffSet
open Langlands.AllField.RankinSelberg.ScalarCutoffProof
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionScalarCutoffStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionScalarCutoff rankOneExtensionWhittakerContraction rankOneWhittakerType zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

section Matrix


end Matrix

section Character


end Character

section Cutoff

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The cutoff set: elements of valuation one congruent to one modulo `π^n`.
Its units are exactly the principal units of level `n`. -/
def cutoffSet (n : ℕ) : Set F :=
  {x | T.discreteValuation x = 1 ∧ (x - 1) / T.uniformizer ^ (n : ℤ) ∈ T.Integers}

theorem mem_cutoffSet_iff (n : ℕ) (u : Fˣ) :
    (u : F) ∈ cutoffSet T n ↔ u ∈ T.principalUnits n :=
  (T.mem_principalUnits_iff_div_mem_integers n u).symm

theorem cutoffSet_isOpen (n : ℕ) :
    letI := T.topology
    IsOpen (cutoffSet T n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hval : IsOpen {x : F | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F x) = 1 ↔
      ValuativeRel.valuation F x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F) := Valuation.isOpen_integer
  have hc : Continuous fun x : F => (x - 1) / T.uniformizer ^ (n : ℤ) :=
    (continuous_id.sub (continuous_const (y := (1 : F)))).div_const _
  exact hval.inter (hint.preimage hc)

theorem cutoffSet_isCompact_isClosed (n : ℕ) :
    letI := T.topology
    IsCompact (cutoffSet T n) ∧ IsClosed (cutoffSet T n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hshell : T.valuationShell 0 = {x | T.discreteValuation x = 1} := by
    ext x
    simp [Langlands.LocalFieldData.valuationShell]
  have hint : IsClosed (T.Integers : Set F) := Valuation.isClosed_integer
  have hclosed : IsClosed (cutoffSet T n) := by
    have hc : Continuous fun x : F => (x - 1) / T.uniformizer ^ (n : ℤ) :=
      (continuous_id.sub (continuous_const (y := (1 : F)))).div_const _
    have h := (T.valuationShell_compact_closed 0).2.inter (hint.preimage hc)
    rw [hshell] at h
    exact h
  refine ⟨(T.valuationShell_compact_closed 0).1.of_isClosed_subset hclosed ?_, hclosed⟩
  intro x hx
  rw [hshell]
  exact hx.1

theorem one_mem_cutoffSet (n : ℕ) : (1 : F) ∈ cutoffSet T n := by
  refine ⟨map_one _, ?_⟩
  rw [sub_self, zero_div]
  exact Subring.zero_mem _

theorem zero_not_mem_cutoffSet (n : ℕ) : (0 : F) ∉ cutoffSet T n := by
  intro h
  have h0 := h.1
  rw [map_zero] at h0
  exact zero_ne_one h0

theorem exists_unit_of_mem_cutoffSet (n : ℕ) {y : F} (hy : y ∈ cutoffSet T n) :
    ∃ a : Fˣ, (a : F) = y ∧ a ∈ T.principalUnits n := by
  have hy0 : y ≠ 0 := fun h => zero_not_mem_cutoffSet T n (h ▸ hy)
  exact ⟨Units.mk0 y hy0, rfl, (mem_cutoffSet_iff T n _).mp hy⟩

end Cutoff

end ScalarCutoffProof

open Langlands.RankinSelberg.ScalarCutoffProof hiding cutoffSet cutoffSet_isCompact_isClosed cutoffSet_isOpen exists_unit_of_mem_cutoffSet mem_cutoffSet_iff one_mem_cutoffSet zero_not_mem_cutoffSet in
open Langlands.AllField.RankinSelberg.ScalarCutoffProof in
/-- The same-model scalar Fourier cutoff for the early JPSS Lemma (5.5). -/
theorem rankOneExtensionScalarCutoff :
    RankOneExtensionScalarCutoffStatement.{uF, uV} := by
  intro F _ _ _ _ ψ ν t k V _ _ π
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : TotallyDisconnectedSpace F :=
    (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
  intro hπ ℓ f₂ χ O hO hO1
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f₂
  obtain ⟨K, hK⟩ := hπ v
  -- Continuity of the scalar diagonal and of the smearing transvection.
  have hφ : Continuous fun a : Fˣ =>
      Units.map (scalarBlockHom (R := F) t) a := by
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        (continuous_matrix fun _ _ => Units.continuous_val) :
          Continuous fun a : Fˣ =>
            Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) F) 0 0
              (Matrix.of fun (_ _ : Fin 1) => a.val))
    · exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        (continuous_matrix fun _ _ => Units.continuous_coe_inv) :
          Continuous fun a : Fˣ =>
            Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) F) 0 0
              (Matrix.of fun (_ _ : Fin 1) => (a⁻¹ : Fˣ).val))
  have hD : Continuous (scalarDiagonal (R := F) t k) :=
    (GeneralLinear.rankInclusionContinuous (k + 1)).continuous.comp
      ((GeneralLinear.reindexContinuous (R := F)
        (rankOneExtensionCellCoordinates t)).continuous.comp hφ)
  have hS : Continuous (rankOneExtensionSmearingUnipotent (K := F) t k) := by
    have hval : Continuous fun u : F =>
        (rankOneExtensionSmearingUnipotent t k u).val := by
      refine continuous_matrix fun i j => ?_
      exact (continuous_const.add (continuous_if_const _ (fun _ => continuous_id)
        (fun _ => continuous_const))).congr
          (fun u => (rankOneExtensionSmearingUnipotent_apply t k u i j).symm)
    rw [Units.continuous_iff]
    exact ⟨hval, hval.comp continuous_neg⟩
  -- The principal-unit level.
  obtain ⟨n₀, hn₀⟩ := (⟨⟩ : LocalFieldData F).exists_multiplicativeTrivialAt χ
  have hDK : {a : Fˣ | scalarDiagonal t k a ∈ K} ∈ 𝓝 (1 : Fˣ) := by
    apply (K.isOpen.preimage hD).mem_nhds
    change scalarDiagonal t k 1 ∈ K
    rw [scalarDiagonal_one]
    exact K.one_mem
  obtain ⟨n₁, hn₁⟩ := (⟨⟩ : LocalFieldData F).exists_principalUnits_subset hDK
  have hOO : (Units.val ⁻¹' O : Set Fˣ) ∈ 𝓝 (1 : Fˣ) :=
    (hO.preimage Units.continuous_val).mem_nhds (by simpa using hO1)
  obtain ⟨n₂, hn₂⟩ := (⟨⟩ : LocalFieldData F).exists_principalUnits_subset hOO
  have hle₀ := (⟨⟩ : LocalFieldData F).principalUnits_antitone
    (show n₀ ≤ n₀ + n₁ + n₂ by omega)
  have hle₁ := (⟨⟩ : LocalFieldData F).principalUnits_antitone
    (show n₁ ≤ n₀ + n₁ + n₂ by omega)
  have hle₂ := (⟨⟩ : LocalFieldData F).principalUnits_antitone
    (show n₂ ≤ n₀ + n₁ + n₂ by omega)
  let U := cutoffSet (⟨⟩ : LocalFieldData F) (n₀ + n₁ + n₂)
  obtain ⟨hUc, hUcl⟩ := cutoffSet_isCompact_isClosed (⟨⟩ : LocalFieldData F) (n₀ + n₁ + n₂)
  have hUo := cutoffSet_isOpen (⟨⟩ : LocalFieldData F) (n₀ + n₁ + n₂)
  have hUχ : ∀ a : Fˣ, (a : F) ∈ U → χ a = 1 := fun a ha =>
    hn₀ a (hle₀ ((mem_cutoffSet_iff _ _ a).mp ha))
  have hfix : ∀ a : Fˣ, (a : F) ∈ U → π (scalarDiagonal t k a) v = v := by
    intro a ha
    have hKa : scalarDiagonal t k a ∈ K.toSubgroup :=
      hn₁ (hle₁ ((mem_cutoffSet_iff _ _ a).mp ha))
    exact (Representation.mem_invariants _ _).mp hK ⟨_, hKa⟩
  -- The Schwartz–Bruhat pair.
  let Φ : SchwartzBruhat F := Hecke.TestFunction.characteristic ⟨hUcl, hUo⟩ hUc
  have hΦ : ∀ b, Φ b = U.indicator (fun _ => (1 : ℂ)) b := fun b => rfl
  let Φneg := Hecke.TestFunction.pullback (Homeomorph.neg F) Φ
  obtain ⟨κ, hκ⟩ := (scalarFourierClosure F ψ ν.val ν.property).2 Φneg
  have hΦκ : ∀ b, Φ b = fourierIntegral ψ ν.val κ b := by
    intro b
    have hfun : (κ : F → ℂ) = fourierTransform ψ ν.val Φneg := funext hκ
    calc Φ b = Φneg (-b) := by simp [Φneg]
      _ = fourierIntegral ψ ν.val (fourierTransform ψ ν.val Φneg) b :=
        ((ν.property Φneg).2 b).symm
      _ = fourierIntegral ψ ν.val κ b := by rw [hfun]
  have hΦin : ∀ a : Fˣ, (a : F) ∈ U → Φ (a : F) = ((χ a : ℂˣ) : ℂ)⁻¹ := by
    intro a ha
    rw [hΦ, Set.indicator_of_mem ha, hUχ a ha]
    simp
  have hΦout : ∀ a : Fˣ, (a : F) ∉ U → Φ (a : F) = 0 := by
    intro a ha
    rw [hΦ, Set.indicator_of_notMem ha]
  -- The smeared coefficient.
  obtain ⟨f₁, hf₁⟩ := Smearing.exists_coefficient_average ν.val.measure π hπ ℓ
    (rankOneExtensionSmearingUnipotent t k) hS κ (modelMap π ℓ v)
  have hcov : ∀ (m : Langlands.GeneralLinear (t + 1) F)
      (x : Fin (t + 1) → F) (a : Fˣ) (u : F),
      κ u * (modelMap π ℓ v).val.val
          (rankOneExtensionEmbeddedLowerBlock t k m x a *
            rankOneExtensionSmearingUnipotent t k u) =
        (ψ.complex (u * a) * κ u) *
          (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) := by
    intro m x a u
    have hθ := (modelMap π ℓ v).val.property
      ⟨rankOneExtensionSmearingUnipotent t k (a.val * u),
        smearing_mem_upperUnipotent t k (a.val * u)⟩
      (rankOneExtensionEmbeddedLowerBlock t k m x a)
    rw [embeddedLowerBlock_mul_smearing]
    erw [hθ]
    rw [standardCharacter_smearing, mul_comm (a.val) u]
    ring
  have hsmear : ∀ (m : Langlands.GeneralLinear (t + 1) F)
      (x : Fin (t + 1) → F) (a : Fˣ),
      f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
        Φ (a : F) *
          (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) := by
    intro m x a
    rw [(hf₁ _).2, funext (hcov m x a), integral_mul_const, hΦκ]
    rfl
  have hscalar : ∀ (m : Langlands.GeneralLinear (t + 1) F)
      (x : Fin (t + 1) → F) (a : Fˣ), (a : F) ∈ U →
      (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
        (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1) := by
    intro m x a ha
    rw [embeddedLowerBlock_eq_mul]
    change ℓ.val (π (rankOneExtensionEmbeddedLowerBlock t k m x 1 * scalarDiagonal t k a) v) =
      ℓ.val (π (rankOneExtensionEmbeddedLowerBlock t k m x 1) v)
    rw [map_mul, Module.End.mul_apply, hfix a ha]
  refine ⟨U, κ, Φ, f₁, hUc, hUo, ?_, one_mem_cutoffSet _ _, zero_not_mem_cutoffSet _ _,
    ?_, ?_, hΦin, hΦout, hΦκ, hf₁, hsmear, hscalar, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, rfl, ha⟩ := exists_unit_of_mem_cutoffSet _ _ hy
    exact hn₂ (hle₂ ha)
  · intro y hy
    exact ((⟨⟩ : LocalFieldData F).normalizedAbs_eq_one_iff_discreteValuation y).mpr hy.1
  · rw [hΦ, Set.indicator_of_notMem (zero_not_mem_cutoffSet _ _)]
  · intro m x a ha
    rw [hsmear, hΦin a ha, hscalar m x a ha]
  · intro m x a ha
    rw [hsmear, hΦout a ha, zero_mul]

end Langlands.AllField.RankinSelberg
