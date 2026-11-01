import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonHaarShear
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSupportedSynthesis
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitSmooth

/-! Exact compact Whittaker pairing with the actual signed Fourier orbit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory HarmonicAnalysis Induction GeneralLinear Whittaker Topology
open GLDeterminantDensity

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance signedCompactPairingTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance signedCompactPairingValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance signedCompactPairingLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance signedCompactPairingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance signedCompactPairingSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance signedCompactPairingSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance signedCompactPairingMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance signedCompactPairingBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance signedCompactPairingGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance signedCompactPairingGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance signedCompactPairingGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance signedCompactPairingGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance signedCompactPairingNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance signedCompactPairingNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedCompactPairingNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance signedCompactPairingNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩


local instance signedCompactPairingTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- A supported matrix lift of the inverse determinant twist of one actual
compact induced function. The lift is chosen independently of the second test. -/
def weightedCompactMatrixLift
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  compactMatrixLift F ψ n (weightedCompactFunction abv
    (PadicField.TopologicalData.isOpenNormOne_of_eq_normalizedAbs (fun _ => rfl))
    n (standardCharacter ψ n) s f)

theorem weightedCompactMatrixLift_support
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    tsupport (weightedCompactMatrixLift F ψ n s f : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  compactMatrixLift_support F ψ n _

theorem weightedCompactMatrixLift_orbit_integrable
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Integrable (fun u : upperUnipotent (n + 1) F.Carrier =>
      (inverseStandardCharacter ψ n u : ℂ) *
        weightedCompactMatrixLift F ψ n s f (u.val * g).val)
      (unipotentHaar F.Carrier n) :=
  compactMatrixLift_orbit_integrable F ψ n _ g

/-- The two inverse determinant powers cancel exactly in the true orbit integral. -/
theorem weightedCompactMatrixLift_orbit
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    determinantWeight abv g s *
      (∫ u : upperUnipotent (n + 1) F.Carrier,
        (inverseStandardCharacter ψ n u : ℂ) *
          weightedCompactMatrixLift F ψ n s f (u.val * g).val
        ∂unipotentHaar F.Carrier n) = eval _ _ f.val g := by
  rw [show (∫ u : upperUnipotent (n + 1) F.Carrier,
      (inverseStandardCharacter ψ n u : ℂ) *
        weightedCompactMatrixLift F ψ n s f (u.val * g).val
      ∂unipotentHaar F.Carrier n) =
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
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ (u, g)
      ∂unipotentHaar F.Carrier n) =
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
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n
        (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f) Ψ (u, g)
      ∂unipotentHaar F.Carrier n) =
    eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val := by
  simp only [signedUnipotentGeneralLinearFourierShearedKernel, integral_const_mul,
    integral_mul_const]
  rw [← mul_assoc, weightedCompactMatrixLift_orbit]

/-- The literal natural-weight signed Fourier orbit of the fixed supported
lift of a compact input. No compact-support claim is made for the output. -/
def signedFourierOrbitOfCompact
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  weightedSignedMatrixOrbit F ψ n (n + 1 : ℕ)
    (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd
      (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f)) g

theorem signedFourierOrbitOfCompact_left
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (u : upperUnipotent (n + 1) F.Carrier)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    signedFourierOrbitOfCompact F ψ ν hsd n f (u.val * g) =
      (standardCharacter ψ n u : ℂ) * signedFourierOrbitOfCompact F ψ ν hsd n f g :=
  weightedSignedMatrixOrbit_left F ψ n (n + 1 : ℕ) _ u g

theorem signedFourierOrbitOfCompact_locallyConstant
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    IsLocallyConstant (signedFourierOrbitOfCompact F ψ ν hsd n f) :=
  weightedSignedMatrixOrbit_locallyConstant F ψ n (n + 1 : ℕ) _

theorem continuous_signedFourierOrbitOfCompact
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    Continuous (signedFourierOrbitOfCompact F ψ ν hsd n f) :=
  (signedFourierOrbitOfCompact_locallyConstant F ψ ν hsd n f).continuous

/-- Compact inputs admit the actual signed-Weyl Fourier pairing with every
second Schwartz test. The proof uses genuine sheared product convergence. -/
theorem integrable_compact_signedWeyl_fourier_pairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val)
      (generalLinearHaar F.Carrier n) := by
  have hi := (integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel
    F ψ ν hsd n (weightedCompactMatrixLift F ψ n (n + 1 : ℕ) f) Ψ
    (weightedCompactMatrixLift_support F ψ n (n + 1 : ℕ) f)).integral_prod_right
  simpa only [integral_signedUnipotentShearedKernel_eq_compactPairing] using hi

/-- The exact compact pairing identity: genuine convergence on both sides,
the original compact input, and the actual signed Fourier orbit of its one
fixed supported lift. The same supplied self-dual measure is used throughout. -/
theorem compact_signedFourier_pairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val)
      (generalLinearHaar F.Carrier n) ∧
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val)
      (generalLinearHaar F.Carrier n) ∧
    (∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val
      ∂generalLinearHaar F.Carrier n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val
      ∂generalLinearHaar F.Carrier n := by
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
        ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
        ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
          signedFourierOrbitOfCompact F ψ ν hsd n f g * Ψ g.val
          ∂generalLinearHaar F.Carrier n := by
      rw [integral_prod_symm _ hd]
      simp only [integral_signedUnipotentDualKernel_eq_weightedOrbit F ψ ν hsd n,
        signedFourierOrbitOfCompact, Φ]
    have hoe : (∫ z, signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z
        ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
        ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
          eval _ _ f.val g * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * g).val
          ∂generalLinearHaar F.Carrier n := by
      rw [integral_prod_symm _ ho]
      simp only [Φ, integral_signedUnipotentShearedKernel_eq_compactPairing]
    exact hde.symm.trans (he.trans
      ((integral_generalLinear_signedUnipotentMatrixFourierShearedKernel
        F ψ ν n Φ Ψ).symm.trans hoe))

end Langlands.RankinSelberg.CompactWhittakerSynthesis
