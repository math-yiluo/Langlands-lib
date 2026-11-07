import Langlands.Automorphic.OperatorDeterminantSliceMeasure
import Langlands.GroupScheme.Lie.GeneralLinearAdjointDeterminant
import Langlands.Global.AdelicLocalModularComparison
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof

/-! # The actual general-linear Haar pairing on a determinant band -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.OperatorDeterminantSlice

open CategoryTheory _root_.AlgebraicGeometry Langlands.Global ContinuousRationalFunctions
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance haarIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance haarSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The actual full adelic GL Haar measure is right invariant. -/
theorem haar_isMulRightInvariant :
    (Measure.haar : Measure (AdelicGroupPoints F (matrixGroupScheme F n))).IsMulRightInvariant := by
  apply AdelicGroupPoints.haarRightInvariant_of_adjointDeterminant_eq_zero
  · exact AdelicGroupPoints.modularCharacter_eq_characterNorm_of_local F
      (matrixGroupScheme F n)
      (Langlands.GroupScheme.Lie.adjointDeterminantCharacter (matrixGroupScheme F n)).toMul
      (PlaceGroupPoints.localModularCharacterAdjointDeterminant F (matrixGroupScheme F n)
        (haarSmooth F n))
  · exact Langlands.GroupScheme.GeneralLinear.adjointDeterminantCharacter_eq_zero (Fin n) F

/-- Every positive right translation preserves the actual principal quotient measure. -/
theorem measurePreserving_translate (g : AdelicGL F n) :
    MeasurePreserving (translate F n g) (quotientHaarMeasure F n) (quotientHaarMeasure F n) := by
  let := haar_isMulRightInvariant F n
  exact AdelicGroupPoints.measurePreserving_rightTranslate_rationalQuotientHaarMeasure
    F (matrixGroupScheme F n) ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g)

variable (S : OperatorRealization F n)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original finite-action form with actual Haar support and invariance discharged. -/
def finiteInvariantPositiveFormOfHaar (hn : n ≠ 0)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space,
      MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n))) :
    Langlands.InvariantPositiveForm S.finiteRepresentation :=
  finiteInvariantPositiveForm F n S hn (quotientHaarMeasure F n) χ hχ hS hL2
    (fun g _ => measurePreserving_translate F n g)

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- A rational covering-set squared-integral bound constructs the original finite form. -/
def finiteInvariantPositiveFormOfCover (hn : n ≠ 0)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n,
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ≤ 2 →
        ∃ a : RationalGL F n, AdelicGL.rational F n a * x ∈ t)
    (hfinite : ∀ f : S.Space,
      (∫⁻ x in t, ‖evaluate F n (S.toContinuous f) x‖ₑ ^ 2 ∂matrixHaarMeasure F n) < ⊤) :
    Langlands.InvariantPositiveForm S.finiteRepresentation :=
  finiteInvariantPositiveFormOfHaar F n S hn χ hχ hS
    (fun f => memLp_band_of_cover F n S t ht hcover f (hfinite f))

end Langlands.Automorphic.OperatorDeterminantSlice
