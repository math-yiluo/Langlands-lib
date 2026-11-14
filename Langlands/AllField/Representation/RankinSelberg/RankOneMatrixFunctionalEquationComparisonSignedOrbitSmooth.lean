import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.AllField.Representation.Shahidi.Induction
/-! Smooth standard-character functions from the actual signed matrix orbit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding exists_signedMatrixOrbit_congruence exists_weightedSignedMatrixOrbit_stabilizer signedMatrixOrbit signedMatrixOrbit_left signedSmoothLocalField signedSmoothNBorel signedSmoothNLocallyCompact signedSmoothNMeasurable signedSmoothTopology signedSmoothValuativeRel weightedSignedMatrixOrbit weightedSignedMatrixOrbitSmooth weightedSignedMatrixOrbitSmooth_eval weightedSignedMatrixOrbit_left weightedSignedMatrixOrbit_locallyConstant
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open Langlands.GeneralLinear
open Langlands.Whittaker

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedSmoothNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).upperUnipotentLocallyCompactSpace (n + 1)
local instance signedSmoothNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance signedSmoothNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The actual signed inverse-transpose orbit of one ambient matrix test. -/
def signedMatrixOrbit (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  ∫ u : upperUnipotent (n + 1) F,
    (inverseStandardCharacter ψ n u : ℂ) *
      Θ (inverseTranspose (n + 1) F u.val * (rankOneSignedWeyl n)⁻¹ * g).val
    ∂unipotentHaar F n

/-- Signed reflection and right Haar substitution give the same standard
character, rather than its inverse. -/
theorem signedMatrixOrbit_left (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    signedMatrixOrbit F ψ n Θ (u.val * g) =
      (standardCharacter ψ n u : ℂ) * signedMatrixOrbit F ψ n Θ g :=
  integral_signedInverseTransposeOrbit_left n (unipotentHaar F n)
    ψ (fun x => Θ x.val) u g

/-- A single principal congruence subgroup fixes the entire orbit function.
No regularity of a parameter-dependent integral is assumed. -/
theorem exists_signedMatrixOrbit_congruence (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      ∀ k ∈ Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup F n m,
        ∀ g : Langlands.GeneralLinear (n + 1) F,
          signedMatrixOrbit F ψ n Θ (g * k) = signedMatrixOrbit F ψ n Θ g := by
  obtain ⟨m₀, hm₀⟩ := Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_schwartz_congruence F Θ
  refine ⟨m₀, fun m hm k hk g => ?_⟩
  unfold signedMatrixOrbit
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [← mul_assoc, Units.val_mul, hm₀ m hm k hk]

/-- The determinant-weighted signed orbit function for any complex exponent. -/
def weightedSignedMatrixOrbit (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (s : ℂ) (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  determinantWeight abv g s * signedMatrixOrbit F ψ n Θ g

/-- The determinant twist is trivial on upper unipotents, so it retains
the same standard-character covariance. -/
theorem weightedSignedMatrixOrbit_left (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
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
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      ∀ (k : L) (g : Langlands.GeneralLinear (n + 1) F),
        weightedSignedMatrixOrbit F ψ n s Θ (g * k.val) =
          weightedSignedMatrixOrbit F ψ n s Θ g := by
  obtain ⟨m, hm⟩ := exists_signedMatrixOrbit_congruence F ψ n Θ
  have hopen : Shahidi.IsOpenNormOne abv :=
    Langlands.LocalFieldData.isOpenNormOne_of_eq_normalizedAbs (T := ⟨⟩) (fun _ => rfl)
  let L₁ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F) :=
    ⟨Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup F n m, Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_congruenceGroup F n m⟩
  let L₂ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F) :=
    ⟨(Shahidi.determinantPower abv (n + 1) s).ker,
      Shahidi.isOpen_ker_determinantPower hopen (n + 1) s⟩
  refine ⟨L₁ ⊓ L₂, fun k g => ?_⟩
  have hk₁ : k.val ∈ Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup F n m := k.property.1
  have hk₂ : Shahidi.determinantPower abv (n + 1) s k.val = 1 := k.property.2
  have hd : determinantWeight abv (g * k.val) s = determinantWeight abv g s := by
    change (Shahidi.determinantPower abv (n + 1) s (g * k.val) : ℂ) = _
    rw [map_mul, hk₂, mul_one]
    rfl
  simp only [weightedSignedMatrixOrbit, hd, hm m le_rfl k.val hk₁ g]

/-- The actual weighted orbit as a smooth induced standard-character function. -/
def weightedSignedMatrixOrbitSmooth (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    SmoothFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)) :=
  smoothFunctionOf _ _ (weightedSignedMatrixOrbit F ψ n s Θ)
    (weightedSignedMatrixOrbit_left F ψ n s Θ)
    (Classical.choose (exists_weightedSignedMatrixOrbit_stabilizer F ψ n s Θ))
    (Classical.choose_spec (exists_weightedSignedMatrixOrbit_stabilizer F ψ n s Θ))

@[simp] theorem weightedSignedMatrixOrbitSmooth_eval
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (g : Langlands.GeneralLinear (n + 1) F) :
    eval _ _ (weightedSignedMatrixOrbitSmooth F ψ n s Θ) g =
      weightedSignedMatrixOrbit F ψ n s Θ g := rfl

/-- In particular the entire weighted orbit is locally constant. -/
theorem weightedSignedMatrixOrbit_locallyConstant
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (Θ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    IsLocallyConstant (weightedSignedMatrixOrbit F ψ n s Θ) :=
  eval_isLocallyConstant _ _ (weightedSignedMatrixOrbitSmooth F ψ n s Θ)

end Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
