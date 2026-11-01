import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedReflection
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeightedSynthesis
import Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-! Smooth standard-character functions from the actual signed matrix orbit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory HarmonicAnalysis Induction GeneralLinear Whittaker Topology

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance signedSmoothTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance signedSmoothValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance signedSmoothLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance signedSmoothT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance signedSmoothSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance signedSmoothMeasurable : MeasurableSpace F.Carrier := borel _
local instance signedSmoothBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance signedSmoothNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance signedSmoothGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance signedSmoothNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedSmoothNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance signedSmoothNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The actual signed inverse-transpose orbit of one ambient matrix test. -/
def signedMatrixOrbit (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  ∫ u : upperUnipotent (n + 1) F.Carrier,
    (inverseStandardCharacter ψ n u : ℂ) *
      Θ (inverseTranspose (n + 1) F.Carrier u.val * (rankOneSignedWeyl n)⁻¹ * g).val
    ∂unipotentHaar F.Carrier n

/-- Signed reflection and right Haar substitution give the same standard
character, rather than its inverse. -/
theorem signedMatrixOrbit_left (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    signedMatrixOrbit F ψ n Θ (u.val * g) =
      (standardCharacter ψ n u : ℂ) * signedMatrixOrbit F ψ n Θ g :=
  integral_signedInverseTransposeOrbit_left n (unipotentHaar F.Carrier n)
    ψ (fun x => Θ x.val) u g

/-- A single principal congruence subgroup fixes the entire orbit function.
No regularity of a parameter-dependent integral is assumed. -/
theorem exists_signedMatrixOrbit_congruence (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      ∀ k ∈ RankOneIwasawa.congruenceGroup F n m,
        ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
          signedMatrixOrbit F ψ n Θ (g * k) = signedMatrixOrbit F ψ n Θ g := by
  obtain ⟨m₀, hm₀⟩ := RankOneIwasawa.exists_schwartz_congruence F Θ
  refine ⟨m₀, fun m hm k hk g => ?_⟩
  unfold signedMatrixOrbit
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [← mul_assoc, Units.val_mul, hm₀ m hm k hk]

/-- The determinant-weighted signed orbit function for any complex exponent. -/
def weightedSignedMatrixOrbit (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (s : ℂ) (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv g s * signedMatrixOrbit F ψ n Θ g

/-- The determinant twist is trivial on upper unipotents, so it retains
the same standard-character covariance. -/
theorem weightedSignedMatrixOrbit_left (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    weightedSignedMatrixOrbit F ψ n s Θ (u.val * g) =
      (standardCharacter ψ n u : ℂ) * weightedSignedMatrixOrbit F ψ n s Θ g := by
  have hd : determinantWeight abv (u.val * g) s = determinantWeight abv g s := by
    change (Shahidi.determinantPower abv (n + 1) s (u.val * g) : ℂ) = _
    rw [map_mul, determinantPower_upperUnipotent, one_mul]
    rfl
  simp only [weightedSignedMatrixOrbit, hd, signedMatrixOrbit_left]
  ring

/-- Intersecting a congruence subgroup with the open determinant-character
kernel supplies a uniform open stabilizer of the weighted orbit. -/
theorem exists_weightedSignedMatrixOrbit_stabilizer
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ (k : L) (g : Langlands.GeneralLinear (n + 1) F.Carrier),
        weightedSignedMatrixOrbit F ψ n s Θ (g * k.val) =
          weightedSignedMatrixOrbit F ψ n s Θ g := by
  obtain ⟨m, hm⟩ := exists_signedMatrixOrbit_congruence F ψ n Θ
  have hopen : Shahidi.IsOpenNormOne abv :=
    PadicField.TopologicalData.isOpenNormOne_of_eq_normalizedAbs (fun _ => rfl)
  let L₁ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    ⟨RankOneIwasawa.congruenceGroup F n m, RankOneIwasawa.isOpen_congruenceGroup F n m⟩
  let L₂ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    ⟨(Shahidi.determinantPower abv (n + 1) s).ker,
      Shahidi.isOpen_ker_determinantPower hopen (n + 1) s⟩
  refine ⟨L₁ ⊓ L₂, fun k g => ?_⟩
  have hk₁ : k.val ∈ RankOneIwasawa.congruenceGroup F n m := k.property.1
  have hk₂ : Shahidi.determinantPower abv (n + 1) s k.val = 1 := k.property.2
  have hd : determinantWeight abv (g * k.val) s = determinantWeight abv g s := by
    change (Shahidi.determinantPower abv (n + 1) s (g * k.val) : ℂ) = _
    rw [map_mul, hk₂, mul_one]
    rfl
  simp only [weightedSignedMatrixOrbit, hd, hm m le_rfl k.val hk₁ g]

/-- The actual weighted orbit as a smooth induced standard-character function. -/
def weightedSignedMatrixOrbitSmooth (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    SmoothFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)) :=
  smoothFunctionOf _ _ (weightedSignedMatrixOrbit F ψ n s Θ)
    (weightedSignedMatrixOrbit_left F ψ n s Θ)
    (Classical.choose (exists_weightedSignedMatrixOrbit_stabilizer F ψ n s Θ))
    (Classical.choose_spec (exists_weightedSignedMatrixOrbit_stabilizer F ψ n s Θ))

@[simp] theorem weightedSignedMatrixOrbitSmooth_eval
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    eval _ _ (weightedSignedMatrixOrbitSmooth F ψ n s Θ) g =
      weightedSignedMatrixOrbit F ψ n s Θ g := rfl

/-- In particular the entire weighted orbit is locally constant. -/
theorem weightedSignedMatrixOrbit_locallyConstant
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    IsLocallyConstant (weightedSignedMatrixOrbit F ψ n s Θ) :=
  eval_isLocallyConstant _ _ (weightedSignedMatrixOrbitSmooth F ψ n s Θ)

/-- Continuity follows from the uniform smoothness argument. -/
theorem continuous_weightedSignedMatrixOrbit
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Continuous (weightedSignedMatrixOrbit F ψ n s Θ) :=
  (weightedSignedMatrixOrbit_locallyConstant F ψ n s Θ).continuous

end Langlands.RankinSelberg.CompactWhittakerSynthesis
