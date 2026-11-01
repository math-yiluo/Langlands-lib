import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth
import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixIntegrability
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.LocalFactor.Euler.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.AdjacentCompactMatrix

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance convergenceTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance convergenceValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance convergenceLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance convergenceT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance convergenceNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance convergenceSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance convergenceSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance convergenceMeasurable : MeasurableSpace F.Carrier := borel _
local instance convergenceBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance convergenceGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance convergenceGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance convergenceGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance convergenceGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The exact real spectral twist used in the adjacent-rank image statement. -/
def realTwistedCharacter (χ₀ : Quasicharacter F.Carrier) (u : ℝ) :
    Quasicharacter F.Carrier :=
  χ₀ * F.canonicalTopologicalData.unramifiedCharacterContinuous
    (LocalFactor.spectralParameter F.canonicalTopologicalData.residueCardinality
      F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ))

theorem norm_realSpectralCharacter (u : ℝ) (a : F.Carrierˣ) :
    ‖(F.canonicalTopologicalData.unramifiedCharacterContinuous
      (LocalFactor.spectralParameter F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ)) a : ℂ)‖ =
      F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ u := by
  change ‖(((LocalFactor.spectralParameter
    (F.canonicalTopologicalData.residueCardinality : ℝ)
    F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ)) ^
    F.canonicalTopologicalData.ord (a : F.Carrier) : ℂˣ) : ℂ)‖ = _
  rw [Units.val_zpow_eq_zpow_val]
  rw [norm_zpow, LocalFactor.spectralParameter_eq_cpow,
    Complex.norm_cpow_eq_rpow_re_of_pos F.canonicalTopologicalData.residueCardinality_real_pos,
    F.canonicalTopologicalData.normalizedAbs_of_ne_zero a.ne_zero,
    ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul F.canonicalTopologicalData.residueCardinality_real_pos.le,
    ← Real.rpow_mul F.canonicalTopologicalData.residueCardinality_real_pos.le]
  congr 1
  simp only [Complex.neg_re, Complex.ofReal_re, Int.cast_neg]
  ring

theorem exists_character_norm_exponent (χ₀ : Quasicharacter F.Carrier) :
    ∃ c : ℝ, ∀ a : F.Carrierˣ,
      ‖(χ₀ a : ℂ)‖ = F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ c := by
  let : NonarchimedeanGroup (GeneralLinear 1 F.Carrier) :=
    F.canonicalTopologicalData.generalLinearNonarchimedean 1
  have hker : IsOpen ((χ₀.toMonoidHom.comp
      (determinant : GeneralLinear 1 F.Carrier →* F.Carrierˣ)).ker :
        Set (GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character _
      (χ₀.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous)
  have hopen : IsOpen (χ₀.toMonoidHom.ker : Set F.Carrierˣ) := by
    have h := hker.preimage (scalarContinuous (n := 1) (R := F.Carrier)).continuous
    change IsOpen {a : F.Carrierˣ | χ₀ (determinant (scalar a : GeneralLinear 1 F.Carrier)) = 1} at h
    change IsOpen {a : F.Carrierˣ | χ₀ a = 1}
    simpa only [scalar, determinant, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, pow_one] using h
  exact (PadicField.TopologicalData.smoothCharacterNormDecomposition F
    F.canonicalTopologicalData χ₀.toMonoidHom hopen).exists

/-- The unique real norm exponent of the arbitrary continuous base character. -/
def characterNormExponent (χ₀ : Quasicharacter F.Carrier) : ℝ :=
  (exists_character_norm_exponent F χ₀).choose

theorem characterNormExponent_spec (χ₀ : Quasicharacter F.Carrier) (a : F.Carrierˣ) :
    ‖(χ₀ a : ℂ)‖ = F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^
      characterNormExponent F χ₀ :=
  (exists_character_norm_exponent F χ₀).choose_spec a

theorem norm_realTwistedCharacter (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (a : F.Carrierˣ) :
    ‖(realTwistedCharacter F χ₀ u a : ℂ)‖ =
      F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^
        (characterNormExponent F χ₀ + u) := by
  change ‖(χ₀ a : ℂ) * (F.canonicalTopologicalData.unramifiedCharacterContinuous
    (LocalFactor.spectralParameter F.canonicalTopologicalData.residueCardinality
      F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ)) a : ℂ)‖ = _
  rw [norm_mul, characterNormExponent_spec F χ₀ a,
    norm_realSpectralCharacter F u a, ← Real.rpow_add
      (F.canonicalTopologicalData.normalizedAbs_pos a.ne_zero)]

/-- The norm of a real determinant weight is its real power. -/
theorem norm_realDeterminantWeight {r : ℕ} (g : GeneralLinear (r + 1) F.Carrier)
    (s : ℝ) :
    ‖determinantWeight abv g (s : ℂ)‖ =
      F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ s := by
  unfold determinantWeight
  simpa only [Complex.ofReal_re, determinant, Matrix.GeneralLinearGroup.val_det_apply,
    normalizedAbsoluteValue_apply] using
    Complex.norm_cpow_eq_rpow_re_of_pos
      ((normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero) (s : ℂ)

/-- Multiplication of determinant weights at the strictly positive determinant norm. -/
theorem determinantWeight_add_exponents {r : ℕ}
    (g : GeneralLinear (r + 1) F.Carrier) (s t : ℂ) :
    determinantWeight abv g (s + t) =
      determinantWeight abv g s * determinantWeight abv g t := by
  apply Complex.cpow_add
  exact_mod_cast (normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero g.det_ne_zero

/-- Compact square-matrix tests become GL Haar integrable as soon as the
character and determinant powers dominate the coefficient pole and Haar density. -/
theorem integrable_of_compact_det_growth (ν : AdditiveHaarMeasure F.Carrier)
    (r : ℕ) (f : GeneralLinear (r + 1) F.Carrier → ℂ) (hf : Continuous f)
    (N : ℕ)
    (hgrowth : ∀ K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier),
      IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
        ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∈ K →
          ‖f g‖ * F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N ≤ C)
    (χ : Quasicharacter F.Carrier) (c : ℝ)
    (hχ : ∀ a : F.Carrierˣ,
      ‖(χ a : ℂ)‖ = F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ c)
    (s : ℝ) (hs : (N : ℝ) + (r + 1 : ℕ) ≤ c + s)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) :
    Integrable (fun g : GeneralLinear (r + 1) F.Carrier =>
      Φ g.val * f g * (χ (determinant g) : ℂ) * determinantWeight abv g (s : ℂ))
        (generalLinearHaar F.Carrier r) := by
  let K := tsupport (Φ : _ → ℂ)
  have hK : IsCompact K := Φ.hasCompactSupport
  obtain ⟨C, hC, hbound⟩ := hgrowth K hK
  let t : ℝ := s - (r + 1 : ℕ)
  let e : ℝ := c + t - N
  have he : 0 ≤ e := by dsimp [e, t]; linarith
  let A : GeneralLinear (r + 1) F.Carrier → ℂ := fun g =>
    Φ g.val * f g * (χ (determinant g) : ℂ) * determinantWeight abv g (t : ℂ)
  have hA : Continuous A :=
    (((Φ.continuous.comp Units.continuous_val).mul hf).mul
      (Units.continuous_val.comp (χ.continuous.comp
        (F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous))).mul
          (continuous_adjacentRank_determinantWeight F _ _)
  have hAzero : ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∉ K → A g = 0 := by
    intro g hg
    simp only [A, image_eq_zero_of_notMem_tsupport hg, zero_mul]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn Φ.continuous.continuousOn
  have hdetc : Continuous fun X : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier =>
      F.canonicalTopologicalData.normalizedAbs X.det ^ e :=
    (Real.continuous_rpow_const he).comp
      (F.canonicalTopologicalData.continuous_normalizedAbs.comp continuous_id.matrix_det)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hdetc.continuousOn
  have hAnorm (g : GeneralLinear (r + 1) F.Carrier) :
      ‖A g‖ = ‖Φ g.val‖ *
        (‖f g‖ * F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N) *
          F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ e := by
    let d := F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier)
    have hd : 0 < d := F.canonicalTopologicalData.normalizedAbs_pos (determinant g).ne_zero
    have hexp : c + t = (N : ℝ) + e := by dsimp [e]; ring
    simp only [A, norm_mul, hχ, norm_realDeterminantWeight]
    change ‖Φ g.val‖ * ‖f g‖ * d ^ c * d ^ t =
      ‖Φ g.val‖ * (‖f g‖ * d ^ N) * d ^ e
    calc
      _ = ‖Φ g.val‖ * ‖f g‖ * (d ^ c * d ^ t) := by ring
      _ = ‖Φ g.val‖ * ‖f g‖ * d ^ ((N : ℝ) + e) := by
        rw [← Real.rpow_add hd, hexp]
      _ = _ := by rw [Real.rpow_add hd, Real.rpow_natCast]; ring
  have hAbound (g : GeneralLinear (r + 1) F.Carrier) (hg : g.val ∈ K) :
      ‖A g‖ ≤ max B 0 * C * max D 0 := by
    rw [hAnorm]
    have hb : ‖Φ g.val‖ ≤ max B 0 := (hB g.val hg).trans (le_max_left _ _)
    have hd : F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ e ≤
        max D 0 := by
      apply le_trans _ (le_max_left _ _)
      have h := hD g.val hg
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, determinant,
        Matrix.GeneralLinearGroup.val_det_apply] using h)
    exact mul_le_mul
      (mul_le_mul hb (hbound g hg)
        (mul_nonneg (norm_nonneg _) (pow_nonneg
          (F.canonicalTopologicalData.normalizedAbs_nonneg _) _))
        (le_max_right _ _)) hd
      (Real.rpow_nonneg (F.canonicalTopologicalData.normalizedAbs_nonneg _) _)
      (mul_nonneg (le_max_right _ _) hC)
  have hi := integrable_natWeight_of_compact_bound F ν r A hA K hK hAzero
    (max B 0 * C * max D 0)
    (mul_nonneg (mul_nonneg (le_max_right _ _) hC) (le_max_right _ _)) hAbound
  convert hi using 1
  funext g
  have hs' : (s : ℂ) = (r + 1 : ℕ) + (t : ℂ) := by dsimp [t]; push_cast; ring
  rw [hs', determinantWeight_add_exponents]
  dsimp [A]
  ring

/-- A single sufficient real-twist threshold chosen before coefficient vectors
and square-matrix tests. No optimality is asserted. -/
def realTwistThreshold (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) : ℝ :=
  (coefficientDeterminantOrder F ψ σ hσ ℓ : ℝ) -
    characterNormExponent F χ₀ + (r + 1 : ℕ) - (r : ℝ) / 2

/-- The exact real spectral twists give genuine GL Haar integrability for
every coefficient vector and every square-matrix Schwartz--Bruhat test above
one uniform threshold. -/
theorem integrable_realTwist_of_threshold
    (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) :
    Integrable (fun g : GeneralLinear (r + 1) F.Carrier =>
      Φ g.val * glModelFunction ψ r σ ℓ W g⁻¹ *
        (realTwistedCharacter F χ₀ u (determinant g) : ℂ) *
          determinantWeight abv g ((r : ℂ) / 2))
      (generalLinearHaar F.Carrier r) := by
  have hs : (coefficientDeterminantOrder F ψ σ hσ ℓ : ℝ) +
      (r + 1 : ℕ) ≤ (characterNormExponent F χ₀ + u) + (r : ℝ) / 2 := by
    dsimp [realTwistThreshold] at hu
    linarith
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
    integrable_of_compact_det_growth F ν r
      (fun g => glModelFunction ψ r σ ℓ W g⁻¹)
      ((glModelFunction_continuous ψ r σ hσ.1.1 ℓ W).comp continuous_inv)
      (coefficientDeterminantOrder F ψ σ hσ ℓ)
      (coefficientDeterminantOrder_spec F ψ σ hσ ℓ W)
      (realTwistedCharacter F χ₀ u) (characterNormExponent F χ₀ + u)
      (norm_realTwistedCharacter F χ₀ u) ((r : ℝ) / 2) hs Φ

/-- Existential form with the real bound preceding the twist, all coefficient
vectors, and all square-matrix tests. -/
theorem exists_integrable_realTwist_bound
    (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) :
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
      ∀ Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier),
        Integrable (fun g : GeneralLinear (r + 1) F.Carrier =>
          Φ g.val * glModelFunction ψ r σ ℓ W g⁻¹ *
            (realTwistedCharacter F χ₀ u (determinant g) : ℂ) *
              determinantWeight abv g ((r : ℂ) / 2))
          (generalLinearHaar F.Carrier r) := by
  exact ⟨realTwistThreshold F ψ σ hσ ℓ χ₀,
    fun u hu W Φ => integrable_realTwist_of_threshold F ν ψ σ hσ ℓ χ₀ u hu W Φ⟩

end Langlands.RankinSelberg.AdjacentCompactMatrix
