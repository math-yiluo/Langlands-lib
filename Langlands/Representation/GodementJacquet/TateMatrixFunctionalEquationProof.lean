import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.TateMatrixAnalyticData
import Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar

/-! The rank-one matrix functional equation with its supplied Fourier measure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV

section FourierTransport

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]

omit [IsTopologicalRing K] [BorelSpace K] in
/-- Unique-entry coordinates identify the full matrix and scalar Fourier
integrals with the exact supplied scalar additive measure. -/
theorem tateRectangularFourierIntegral_eq
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (Φ : MatrixTestFunction 0 K) (X : Matrix (Fin 1) (Fin 1) K) :
    rectangularFourierIntegral ψ ν Φ X =
      fourierIntegral ψ ν (tateScalarTest K Φ) (X 0 0) := by
  unfold rectangularFourierIntegral fourierIntegral
  have h := (oneByOneScalarEquiv_measurePreserving ν).integral_comp
    oneByOneScalarEquiv.measurableEmbedding
    (fun a => ψ.complex (a * X 0 0) * tateScalarTest K Φ a)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with A
  have hpair : rectangularPairing A X = A 0 0 * X 0 0 := by
    change (∑ i : Fin 1, ∑ j : Fin 1, A i j * X i j) = _
    simp only [Fin.sum_univ_one]
  have htest : tateScalarTest K Φ (A 0 0) = Φ A := by
    change Φ (fun _ _ => A 0 0) = Φ A
    apply congrArg (fun M : Matrix (Fin 1) (Fin 1) K => Φ M)
    funext i j
    fin_cases i
    fin_cases j
    rfl
  simp only [oneByOneScalarEquiv_apply, hpair, htest]
  exact mul_comm _ _

omit [IsTopologicalRing K] [BorelSpace K] in
/-- An integrable scalar Fourier pair transports to a full matrix pair. -/
theorem tateMatrixFourierPair_of_scalar
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (Φ : MatrixTestFunction 0 K) (φhat : SchwartzBruhat K)
    (h : ∀ y, Integrable (fun x => ψ.complex (x * y) * tateScalarTest K Φ x)
      ν.measure ∧ φhat y = fourierIntegral ψ ν (tateScalarTest K Φ) y) :
    GodementJacquet.MatrixFourierPair ψ ν Φ
      (Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph K) φhat) := by
  intro X
  refine ⟨?_, ?_⟩
  · have hi := ((oneByOneScalarEquiv_measurePreserving ν).integrable_comp_emb
        oneByOneScalarEquiv.measurableEmbedding).mpr (h (X 0 0)).1
    convert hi using 1
    funext A
    have hpair : rectangularPairing A X = A 0 0 * X 0 0 := by
      change (∑ i : Fin 1, ∑ j : Fin 1, A i j * X i j) = _
      simp only [Fin.sum_univ_one]
    have htest : tateScalarTest K Φ (A 0 0) = Φ A := by
      change Φ (fun _ _ => A 0 0) = Φ A
      apply congrArg (fun M : Matrix (Fin 1) (Fin 1) K => Φ M)
      funext i j
      fin_cases i
      fin_cases j
      rfl
    simp only [Function.comp_apply, oneByOneScalarEquiv_apply, hpair, htest]
    exact mul_comm _ _
  · change φhat (X 0 0) = _
    rw [(h (X 0 0)).2, tateRectangularFourierIntegral_eq]

/-- Linearity identifies any Fourier witness of a scaled test with the same
scalar multiple of a previously supplied witness, including scalar zero. -/
theorem tateScalarFourierWitness_smul
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (φ φhat ψhat : SchwartzBruhat K) (k : ℂ)
    (hφ : ∀ y, φhat y = fourierIntegral ψ ν φ y)
    (hψ : ∀ y, ψhat y = fourierIntegral ψ ν (k • φ) y) :
    ψhat = k • φhat := by
  apply Subtype.ext
  funext y
  change ψhat y = k * φhat y
  rw [hψ, hφ]
  exact congrFun ((fourierTransform ψ ν).map_smul k φ) y

end FourierTransport

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance tateProofTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance tateProofValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance tateProofLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance tateProofT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance tateProofTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance tateProofMeasurable : MeasurableSpace F.Carrier := borel _
local instance tateProofBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance tateProofUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance tateProofUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance tateProofGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance tateProofGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]

/-- A proved scalar action on the actual carrier gives the full matrix data.
The Fourier witness is chosen before every coefficient and continuation. -/
theorem exists_tateMatrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν)
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a := by
  have hinv (x : F.Carrierˣ) : ((χ⁻¹) x : ℂ) = (χ x : ℂ)⁻¹ :=
    Units.val_inv_eq_inv_val (χ x)
  obtain ⟨P, hP⟩ := exists_tateMatrixAnalyticAssertions F σ χ hσ hact
  obtain ⟨PDual, hPDual⟩ := exists_tateIotaMatrixAnalyticAssertions F σ χ hσ hact
  have hPscalar : IsNormalizedGenerator
      (scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun x => (χ x : ℂ)) 1) P := by
    have h := hP.2.2
    change IsNormalizedGenerator (matrixRationalValues F σ) P at h
    rwa [tateMatrixRationalValues_eq_scalar F σ χ hσ hact] at h
  have hPDualScalar : IsNormalizedGenerator
      (scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun x => ((χ x)⁻¹ : ℂ)) 1) PDual := by
    have h := hPDual.2.2
    change IsNormalizedGenerator (iotaMatrixRationalValues F σ) PDual at h
    rw [tateIotaMatrixRationalValues_eq_scalar F σ χ hσ hact] at h
    simpa only [hinv] using h
  obtain ⟨c, a, hFE⟩ := tateScalarFunctionalEquation F ψ χ ν hν hPscalar hPDualScalar
  refine ⟨P, PDual, c, a, hP, hPDual, fun Φ => ?_⟩
  obtain ⟨φhat, hFourier, -⟩ := hFE (tateScalarTest F.Carrier Φ)
  let Φhat : MatrixTestFunction 0 F.Carrier :=
    Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F.Carrier) φhat
  refine ⟨Φhat, tateMatrixFourierPair_of_scalar ψ ν Φ φhat hFourier, ?_⟩
  intro f R RDual hR hRDual
  obtain ⟨ψhat, hScaledFourier, hScaledFE⟩ :=
    hFE (f.val 1 • tateScalarTest F.Carrier Φ)
  have hScaled : ψhat = f.val 1 • φhat :=
    tateScalarFourierWitness_smul ψ ν (tateScalarTest F.Carrier Φ) φhat ψhat
      (f.val 1) (fun y => (hFourier y).2) (fun y => (hScaledFourier y).2)
  have hOriginal := (tateHasShiftedRationalValue_iff F χ f.val
    (tateCoefficient_eq σ χ hact f) Φ R).mp hR
  have hiota1 : coefficientIota f.val 1 = f.val 1 := by
    simp [coefficientIota]
  have hiota : ∀ g, coefficientIota f.val g =
      coefficientIota f.val 1 * ((χ⁻¹) (determinant g) : ℂ) := by
    intro g
    change f.val (inverseTranspose 1 F.Carrier g) = _
    rw [hiota1, tateCoefficient_eq σ χ hact f,
      tateInverseTranspose_eq_inv, map_inv, map_inv]
    rfl
  have hDual := (tateHasShiftedRationalValue_iff F χ⁻¹ (coefficientIota f.val)
    hiota Φhat RDual).mp hRDual
  have hTest : tateScalarTest F.Carrier Φhat = φhat :=
    (Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F.Carrier)).left_inv φhat
  rw [hiota1, hTest] at hDual
  rw [hScaled] at hScaledFE
  exact hScaledFE R RDual hOriginal (by simpa only [hinv] using hDual)

end Padic

/-- Full rank-one Godement--Jacquet functional equation for the original
admissible irreducible representation and the supplied self-dual measure. -/
theorem tateMatrixFunctionalEquation : TateMatrixFunctionalEquationStatement.{uF,uV} := by
  intro p hp F ψ ν hν V hV hModule σ ha hi
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  let : MeasurableSpace (Langlands.GeneralLinear 1 F.Carrier) := borel _
  let : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Langlands.GeneralLinear 1 F.Carrier)) σ.asModule
  obtain ⟨χ, ⟨e⟩⟩ := exists_tateCharacterModel σ ha hi
  have hact : TateCharacterAction σ χ := by
    intro g v
    apply e.injective
    rw [map_smul]
    have h := Representation.IntertwiningMap.isIntertwining σ
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) e.toIntertwiningMap g v
    simpa [rankOneCharacter, characterRepresentation, twist] using h
  exact Padic.exists_tateMatrixFunctionalEquationData F ψ ν hν σ χ ha.1 hact

end Langlands.GodementJacquet
