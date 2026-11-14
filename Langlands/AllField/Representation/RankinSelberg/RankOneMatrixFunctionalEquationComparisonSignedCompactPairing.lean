import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonHaarShear
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSupportedSynthesis
/-! Exact compact Whittaker pairing with the actual signed Fourier orbit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding compactMatrixLift compactMatrixLift_orbit compactMatrixLift_support compact_signedFourier_pairing continuous_signedFourierOrbitOfCompact exists_signedMatrixOrbit_congruence exists_supported_compactMatrixLift exists_weightedSignedMatrixOrbit_stabilizer firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_compact_signedWeyl_fourier_pairing integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentDualKernel_eq_weightedOrbit integral_signedUnipotentMatrixFourierKernel_fixed integral_signedUnipotentShearedKernel_eq_compactPairing signedCompactPairingBorelSpace signedCompactPairingGLBorelSpace signedCompactPairingGLLocallyCompact signedCompactPairingGLMeasurableSpace signedCompactPairingGLSecondCountable signedCompactPairingLocalField signedCompactPairingMeasurableSpace signedCompactPairingNBorelSpace signedCompactPairingNLocallyCompact signedCompactPairingNMeasurableSpace signedCompactPairingNSecondCountable signedCompactPairingT2 signedCompactPairingTopology signedCompactPairingTotallyDisconnected signedCompactPairingValuativeRel signedFourierOrbitOfCompact signedFourierOrbitOfCompact_left signedFourierOrbitOfCompact_locallyConstant signedMatrixOrbit signedMatrixOrbit_left signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedSmoothLocalField signedSmoothNBorel signedSmoothNLocallyCompact signedSmoothNMeasurable signedSmoothTopology signedSmoothValuativeRel signedUnipotentMatrixFourier_exchange supportedSynthesisLocalField supportedSynthesisNBorel supportedSynthesisNMeasurable supportedSynthesisT2 supportedSynthesisTopology supportedSynthesisValuativeRel weightedCompactMatrixLift weightedCompactMatrixLift_orbit weightedCompactMatrixLift_support weightedSignedMatrixOrbit weightedSignedMatrixOrbitSmooth weightedSignedMatrixOrbitSmooth_eval weightedSignedMatrixOrbit_left weightedSignedMatrixOrbit_locallyConstant
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight generalLinear_signedUnipotentMatrixFourier_exchange glFourierGLBorelSpace glFourierGLMeasurableSpace glFourierLocalField glFourierMeasurableSpace glFourierTopology glFourierValuativeRel haarShearBorel haarShearGLBorel haarShearGLLocallyCompact haarShearGLMeasurable haarShearGLSecondCountable haarShearLocalField haarShearMeasurable haarShearNBorel haarShearNLocallyCompact haarShearNMeasurable haarShearNSecondCountable haarShearT2 haarShearTopology haarShearTotallyDisconnected haarShearValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_generalLinear_signedUnipotentMatrixFourierDualKernel integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel integrable_prod_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff_full integral_generalLinearHaar_natWeight integral_generalLinear_signedUnipotentMatrixFourierDualKernel integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel integral_generalLinear_signedUnipotentMatrixFourierShearedKernel integral_prod_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight_full padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos rectangularMeasure_ae_det_ne_zero rectangularMeasure_restrict_generalLinear signedGLFourierBorelSpace signedGLFourierGLBorelSpace signedGLFourierGLMeasurableSpace signedGLFourierGLSecondCountable signedGLFourierLocalField signedGLFourierMeasurableSpace signedGLFourierNBorelSpace signedGLFourierNLocallyCompact signedGLFourierNMeasurableSpace signedGLFourierNSecondCountable signedGLFourierT2 signedGLFourierTopology signedGLFourierTotallyDisconnected signedGLFourierValuativeRel signedUnipotentGeneralLinearFourierDualKernel signedUnipotentGeneralLinearFourierOriginalKernel signedUnipotentGeneralLinearFourierOriginalKernel_shear signedUnipotentGeneralLinearFourierShearedKernel singularNullBorelSpace singularNullLocalField singularNullMeasurableSpace singularNullPuncturedNhds singularNullSecondCountable singularNullSigmaCompact singularNullT2 singularNullTopology singularNullValuativeRel weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedCompactPairingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance signedCompactPairingMeasurableSpace : MeasurableSpace F := borel _
local instance signedCompactPairingBorelSpace : BorelSpace F := ⟨rfl⟩
local instance signedCompactPairingGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance signedCompactPairingGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance signedCompactPairingGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance signedCompactPairingGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance signedCompactPairingNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).upperUnipotentLocallyCompactSpace (n + 1)
local instance signedCompactPairingNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedCompactPairingNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance signedCompactPairingNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

local instance signedCompactPairingTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- A supported matrix lift of the inverse determinant twist of one actual
compact induced function. The lift is chosen independently of the second test. -/
def weightedCompactMatrixLift
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  compactMatrixLift F ψ n (weightedCompactFunction abv
    (Langlands.LocalFieldData.isOpenNormOne_of_eq_normalizedAbs (T := ⟨⟩) (fun _ => rfl))
    n (standardCharacter ψ n) s f)

theorem weightedCompactMatrixLift_support
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    tsupport (weightedCompactMatrixLift F ψ n s f : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  compactMatrixLift_support F ψ n _

/-- The two inverse determinant powers cancel exactly in the true orbit integral. -/
theorem weightedCompactMatrixLift_orbit
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F) :
    determinantWeight abv g s *
      (∫ u : upperUnipotent (n + 1) F,
        (inverseStandardCharacter ψ n u : ℂ) *
          weightedCompactMatrixLift F ψ n s f (u.val * g).val
        ∂unipotentHaar F n) = eval _ _ f.val g := by
  rw [show (∫ u : upperUnipotent (n + 1) F,
      (inverseStandardCharacter ψ n u : ℂ) *
        weightedCompactMatrixLift F ψ n s f (u.val * g).val
      ∂unipotentHaar F n) =
      determinantWeight abv g (-s) * eval _ _ f.val g from
    compactMatrixLift_orbit F ψ n _ g]
  have hw : determinantWeight abv g s * determinantWeight abv g (-s) = 1 := by
    change (Shahidi.determinantPower abv (n + 1) s g : ℂ) *
      (Shahidi.determinantPower abv (n + 1) (-s) g : ℂ) = 1
    rw [Shahidi.determinantPower_neg, MonoidHom.inv_apply, Units.mul_inv]
  rw [← mul_assoc, hw, one_mul]

/-- The inner dual kernel is literally the weighted signed Fourier orbit,
multiplied by the same second test. No convergence premise is used here. -/
theorem integral_signedUnipotentDualKernel_eq_weightedOrbit
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (∫ u : upperUnipotent (n + 1) F,
      signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ (u, g)
      ∂unipotentHaar F n) =
    weightedSignedMatrixOrbit F ψ n (n + 1 : ℕ)
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ) g * Ψ g.val := by
  simp only [signedUnipotentGeneralLinearFourierDualKernel,
    signedUnipotentMatrixFourierDualKernel, weightedSignedMatrixOrbit,
    signedMatrixOrbit, rectangularFourierEquiv_apply, Units.val_mul,
    integral_const_mul, integral_mul_const]
  rw [mul_assoc]

/-- The sheared original kernel reconstructs the input compact function at
its natural determinant weight, pointwise at every group element. -/
theorem integral_signedUnipotentShearedKernel_eq_compactPairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (∫ u : upperUnipotent (n + 1) F,
      signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n
        (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f) Ψ (u, g)
      ∂unipotentHaar F n) =
    eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val := by
  simp only [signedUnipotentGeneralLinearFourierShearedKernel, integral_const_mul,
    integral_mul_const]
  rw [← mul_assoc, weightedCompactMatrixLift_orbit]

/-- The literal natural-weight signed Fourier orbit of the fixed supported
lift of a compact input. No compact-support claim is made for the output. -/
def signedFourierOrbitOfCompact
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  weightedSignedMatrixOrbit F ψ n (n + 1 : ℕ)
    (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd
      (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f)) g

theorem signedFourierOrbitOfCompact_left
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    signedFourierOrbitOfCompact F ψ ν hsd n f (u.val * g) =
      (standardCharacter ψ n u : ℂ) * signedFourierOrbitOfCompact F ψ ν hsd n f g :=
  weightedSignedMatrixOrbit_left F ψ n (n + 1 : ℕ) _ u g

theorem signedFourierOrbitOfCompact_locallyConstant
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    IsLocallyConstant (signedFourierOrbitOfCompact F ψ ν hsd n f) :=
  weightedSignedMatrixOrbit_locallyConstant F ψ n (n + 1 : ℕ) _

theorem continuous_signedFourierOrbitOfCompact
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    Continuous (signedFourierOrbitOfCompact F ψ ν hsd n f) :=
  (signedFourierOrbitOfCompact_locallyConstant F ψ ν hsd n f).continuous

/-- Compact inputs admit the actual signed-Weyl Fourier pairing with every
second Schwartz test. The proof uses genuine sheared product convergence. -/
theorem integrable_compact_signedWeyl_fourier_pairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F =>
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val)
      (generalLinearHaar F n) := by
  have hi := (integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel
    F ψ ν hsd n (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f) Ψ
    (weightedCompactMatrixLift_support F ψ n (n + 1 : ℕ) f)).integral_prod_right
  simpa only [integral_signedUnipotentShearedKernel_eq_compactPairing] using hi

/-- The exact compact pairing identity: genuine convergence on both sides,
the original compact input, and the actual signed Fourier orbit of its one
fixed supported lift. The same supplied self-dual measure is used throughout. -/
theorem compact_signedFourier_pairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F =>
      signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val)
      (generalLinearHaar F n) ∧
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F =>
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val)
      (generalLinearHaar F n) ∧
    (∫ g : Langlands.GeneralLinear (n + 1) F,
      signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val
      ∂generalLinearHaar F n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F,
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val
      ∂generalLinearHaar F n := by
  let Φ := weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f
  have hΦ := weightedCompactMatrixLift_support F ψ n (n + 1 : ℕ) f
  obtain ⟨hd, _, he⟩ := generalLinear_signedUnipotentMatrixFourier_exchange
    F ψ ν hsd n Φ Ψ hΦ A q ha hΨ
  have ho := integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel
    F ψ ν hsd n Φ Ψ hΦ
  refine ⟨?_, integrable_compact_signedWeyl_fourier_pairing F ψ ν hsd n f Ψ, ?_⟩
  · simpa only [integral_signedUnipotentDualKernel_eq_weightedOrbit F ψ ν hsd n,
      signedFourierOrbitOfCompact, Φ] using hd.integral_prod_right
  · have hde : (∫ z, signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
        ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
        ∫ g : Langlands.GeneralLinear (n + 1) F,
          signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val
          ∂generalLinearHaar F n := by
      rw [integral_prod_symm _ hd]
      simp only [integral_signedUnipotentDualKernel_eq_weightedOrbit F ψ ν hsd n,
        signedFourierOrbitOfCompact, Φ]
    have hoe : (∫ z, signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z
        ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
        ∫ g : Langlands.GeneralLinear (n + 1) F,
          eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val
          ∂generalLinearHaar F n := by
      rw [integral_prod_symm _ ho]
      simp only [Φ, integral_signedUnipotentShearedKernel_eq_compactPairing]
    exact hde.symm.trans (he.trans
      ((integral_generalLinear_signedUnipotentMatrixFourierShearedKernel
        F ψ ν n Φ Ψ).symm.trans hoe))

end Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
