import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAveraging
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

/-!
# Fourier-compatible averaging and conditional model functional equations

The averaging subgroup depends only on the original full-matrix test.
The same actual coefficient works with every supplied Fourier partner.
Original and inverse-transpose convergence remain hypotheses.
-/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg
open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fourierAveragingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fourierAveragingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fourierAveragingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fourierAveragingScalarMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance fourierAveragingScalarBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance fourierAveragingMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance fourierAveragingBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- A compact open averaging subgroup chosen from the original matrix test
alone, before a Fourier partner or model vector is supplied. -/
def matrixTestAveragingSubgroup (Φ : MatrixTestFunction n F.Carrier) :
    OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  (exists_compactOpen_matrixTest_invariant F Φ).choose

theorem matrixTestAveragingSubgroup_spec (Φ : MatrixTestFunction n F.Carrier) :
    IsCompact (matrixTestAveragingSubgroup F Φ :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
      ∀ k ∈ matrixTestAveragingSubgroup F Φ,
        (∀ M, Φ (k.val * M) = Φ M) ∧
          normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 :=
  (exists_compactOpen_matrixTest_invariant F Φ).choose_spec

/-- The preimage subgroup used by averaging is the image subgroup appearing
in actual Fourier covariance, because inverse transpose is involutive. -/
theorem inverseTransposeOpenSubgroup_toSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) :
    (inverseTransposeOpenSubgroup F K).toSubgroup =
      K.toSubgroup.map (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨GeneralLinear.inverseTranspose (n + 1) F.Carrier g, hg, ?_⟩
    exact GeneralLinear.inverseTranspose_involutive (n + 1) F.Carrier g
  · rintro ⟨k, hk, rfl⟩
    change GeneralLinear.inverseTranspose (n + 1) F.Carrier
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier k) ∈ K
    rw [GeneralLinear.inverseTranspose_involutive]
    exact hk

/-- The chosen subgroup also fixes every actual Fourier partner on the
inverse-transpose side, with determinant norm one there. -/
theorem matrixTestAveragingSubgroup_fourier_spec
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (Φ ΦHat : MatrixTestFunction n F.Carrier) (hpair : MatrixFourierPair F ψ ν Φ ΦHat) :
    ∀ k ∈ inverseTransposeOpenSubgroup F (matrixTestAveragingSubgroup F Φ),
      (∀ M, ΦHat (k.val * M) = ΦHat M) ∧
        normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 := by
  let K := matrixTestAveragingSubgroup F Φ
  have hK := matrixTestAveragingSubgroup_spec F Φ
  have hΦ : Φ ∈ rectangularLeftInvariantTests K.toSubgroup :=
    fun g hg => (hK.2 g hg).1
  have hd := GodementJacquet.padicMatrixFourierPair_compact_left_invariant F
    F.canonicalTopologicalData n ψ ν K.toSubgroup hK.1 Φ ΦHat hpair hΦ
  intro k hk
  constructor
  · apply hd k
    rw [← inverseTransposeOpenSubgroup_toSubgroup F K]
    exact hk
  · have hn := F.canonicalTopologicalData.determinantNorm_eq_one_of_mem_compact
      (n + 1) (inverseTransposeOpenSubgroup F K).toSubgroup
      (isCompact_inverseTransposeOpenSubgroup F K hK.1) k hk
    have hn' := congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hn
    exact hn'

/-- The actual normalized bi-smooth coefficient with subgroup chosen from
the original test alone. -/
def fourierAveragedModelCoefficient (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F.Carrier)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  averagedModelCoefficient F ψ σ hσ ℓ (matrixTestAveragingSubgroup F Φ)
    (matrixTestAveragingSubgroup_spec F Φ).1 w

/-- The original test and any of its actual Fourier partners use one and the
same coefficient. Both original convergence assumptions remain explicit. -/
theorem fourierAveragedModelCoefficient_paired_integrals
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ ΦHat : MatrixTestFunction n F.Carrier) (hpair : MatrixFourierPair F ψ ν Φ ΦHat)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s t : ℂ)
    (hc : MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w))
    (hcd : MatrixConverges F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w))) :
    let f := fourierAveragedModelCoefficient F ψ σ hσ ℓ Φ w
    MatrixConverges F Φ s f.val ∧
      matrixIntegral F Φ s f.val = matrixIntegral F Φ s (glModelFunction ψ n σ ℓ w) ∧
      MatrixConverges F ΦHat t (coefficientIota f.val) ∧
      matrixIntegral F ΦHat t (coefficientIota f.val) =
        matrixIntegral F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w)) :=
  averagedModelCoefficient_paired_integrals F ψ σ hσ ℓ
    (matrixTestAveragingSubgroup F Φ) (matrixTestAveragingSubgroup_spec F Φ).1
    Φ ΦHat (matrixTestAveragingSubgroup_spec F Φ).2
    (matrixTestAveragingSubgroup_fourier_spec F ψ ν Φ ΦHat hpair) w s t hc hcd

/-- Under convergence of the two original functions, the one chosen
coefficient has exactly the same shifted rational values on both sides. -/
theorem fourierAveragedModelCoefficient_rationalValues_iff
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ ΦHat : MatrixTestFunction n F.Carrier) (hpair : MatrixFourierPair F ψ ν Φ ΦHat)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (hc : ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ (glModelFunction ψ n σ ℓ w))
    (hcd : ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) ΦHat
      (coefficientIota (glModelFunction ψ n σ ℓ w)))
    (R RDual : RationalFunctions) :
    let f := fourierAveragedModelCoefficient F ψ σ hσ ℓ Φ w
    (HasShiftedRationalValue q (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ f.val R ↔
      HasShiftedRationalValue q (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ (glModelFunction ψ n σ ℓ w) R) ∧
    (HasShiftedRationalValue q (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) ΦHat (coefficientIota f.val) RDual ↔
      HasShiftedRationalValue q (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) ΦHat
        (coefficientIota (glModelFunction ψ n σ ℓ w)) RDual) := by
  let f := fourierAveragedModelCoefficient F ψ σ hσ ℓ Φ w
  obtain ⟨a, ha⟩ := hc
  obtain ⟨b, hb⟩ := hcd
  have hp (s : ℂ) (hs : max a b < s.re) :=
    fourierAveragedModelCoefficient_paired_integrals F ψ ν σ hσ ℓ Φ ΦHat hpair w
      (s + jpssShift n) (s + jpssShift n)
      (ha s ((le_max_left a b).trans_lt hs))
      (hb s ((le_max_right a b).trans_lt hs))
  have hf : ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ f.val :=
    ⟨max a b, fun s hs => (hp s hs).1⟩
  have hfd : ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) ΦHat (coefficientIota f.val) :=
    ⟨max a b, fun s hs => (hp s hs).2.2.1⟩
  constructor
  · constructor
    · intro hR
      exact ⟨⟨a, ha⟩, RationalContinuationLinear.continuation_of_eq_on_right hR.2
        ⟨max a b, fun s hs => (hp s hs).2.1.symm⟩⟩
    · intro hR
      exact ⟨hf, RationalContinuationLinear.continuation_of_eq_on_right hR.2
        ⟨max a b, fun s hs => (hp s hs).2.1⟩⟩
  · constructor
    · intro hR
      exact ⟨⟨b, hb⟩, RationalContinuationLinear.continuation_of_eq_on_right hR.2
        ⟨max a b, fun s hs => (hp s hs).2.2.2.symm⟩⟩
    · intro hR
      exact ⟨hfd, RationalContinuationLinear.continuation_of_eq_on_right hR.2
        ⟨max a b, fun s hs => (hp s hs).2.2.2⟩⟩

/-- Actual matrix data give the normalized equation for all rational values
of the original model functions, with the same Fourier witness and scalar. -/
theorem normalizedMatrixFunctionalEquationData_model_values
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ)
    (hData : NormalizedMatrixFunctionalEquationData F ψ ν
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P PDual c m)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ ΦHat : MatrixTestFunction n F.Carrier,
      MatrixFourierPair F ψ ν Φ ΦHat ∧
      ∀ w : (glCoefficientModel ψ n σ ℓ).toSubmodule,
        ∀ R RDual : RationalFunctions,
          HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (generalLinearHaar F.Carrier n) Φ (glModelFunction ψ n σ ℓ w) R →
          HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (generalLinearHaar F.Carrier n) ΦHat
            (coefficientIota (glModelFunction ψ n σ ℓ w)) RDual →
          NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
            P PDual 1 c 0 m R RDual := by
  obtain ⟨ΦHat, hpair, hFE⟩ := hData.2.2 Φ
  refine ⟨ΦHat, hpair, ?_⟩
  intro w R RDual hR hRDual
  have hiff := fourierAveragedModelCoefficient_rationalValues_iff F
    F.canonicalTopologicalData.residueCardinality ψ ν σ hσ ℓ Φ ΦHat hpair
    w hR.1 hRDual.1 R RDual
  exact hFE (fourierAveragedModelCoefficient F ψ σ hσ ℓ Φ w) R RDual
    (hiff.1.mpr hR) (hiff.2.mpr hRDual)

/-- Matrix analytic assertions also supply original rational values once
convergence of the original and inverse-transpose functions is available. -/
theorem normalizedMatrixFunctionalEquationData_model_exists
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ)
    (hData : NormalizedMatrixFunctionalEquationData F ψ ν
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P PDual c m)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ ΦHat : MatrixTestFunction n F.Carrier,
      MatrixFourierPair F ψ ν Φ ΦHat ∧
      ∀ w : (glCoefficientModel ψ n σ ℓ).toSubmodule,
        ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier n) Φ (glModelFunction ψ n σ ℓ w) →
        ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier n) ΦHat
          (coefficientIota (glModelFunction ψ n σ ℓ w)) →
        ∃ R RDual : RationalFunctions,
          HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (generalLinearHaar F.Carrier n) Φ (glModelFunction ψ n σ ℓ w) R ∧
          HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (generalLinearHaar F.Carrier n) ΦHat
            (coefficientIota (glModelFunction ψ n σ ℓ w)) RDual ∧
          NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
            P PDual 1 c 0 m R RDual := by
  obtain ⟨ΦHat, hpair, hFE⟩ := hData.2.2 Φ
  refine ⟨ΦHat, hpair, ?_⟩
  intro w hc hcd
  let f := fourierAveragedModelCoefficient F ψ σ hσ ℓ Φ w
  obtain ⟨R, hR⟩ := hData.1.2.1 Φ f
  obtain ⟨RDual, hRDual⟩ := hData.2.1.2.1 ΦHat f
  have hiff := fourierAveragedModelCoefficient_rationalValues_iff F
    F.canonicalTopologicalData.residueCardinality ψ ν σ hσ ℓ Φ ΦHat hpair
    w hc hcd R RDual
  exact ⟨R, RDual, hiff.1.mp hR, hiff.2.mp hRDual, hFE f R RDual hR hRDual⟩

end Langlands.GodementJacquet.Padic
