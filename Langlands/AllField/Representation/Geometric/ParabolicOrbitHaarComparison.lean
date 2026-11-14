import Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
import Langlands.AllField.Group.GL.BlockModulusHaarProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Geometric.ParabolicOrbitNestedAction
import Langlands.AllField.Representation.Geometric.RefinedPositiveCharacter
/-! Identification of the actual nested Haar ratio with ambient characters. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Induction hiding SmoothRep
open scoped NNReal

universe uF

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable [TopologicalSpace F] [IsTopologicalRing F]

section Haar


end Haar

end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open scoped NNReal

universe uF

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- The actual ambient radical Haar character is the explicit block modulus. -/
theorem parabolicOrbitStagesRadicalModulus
    (l : parabolicOrbitStagesQuotient F B C w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    HaarModulus.closedNormalizerCharacter (C.unipotentSubgroup F)
        (C.isClosed_unipotentSubgroup F)
        (parabolicOrbitStagesRadicalNormalizer F B C w l) =
      T.leviModulus C l.val := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace (C.unipotentSubgroup F) :=
    (C.isClosed_unipotentSubgroup F).locallyCompactSpace
  let : MeasurableSpace (C.unipotentRadical F) := borel _
  let : BorelSpace (C.unipotentRadical F) := ⟨rfl⟩
  let : MeasurableSpace (C.unipotentSubgroup F) := borel _
  let : BorelSpace (C.unipotentSubgroup F) := ⟨rfl⟩
  let a := HaarModulus.normalizerConj (C.unipotentRadical F)
    ⟨C.leviInParabolic F l.val, by
      rw [Subgroup.normalizer_eq_top]
      trivial⟩
  let b := HaarModulus.normalizerConj (C.unipotentSubgroup F)
    (parabolicOrbitStagesRadicalNormalizer F B C w l)
  have hc := haarChar_eq_of_conjugacy (C.unipotentRadicalAmbientEquiv F)
    a b (by intro u; apply Subtype.ext; rfl)
  apply Units.ext
  change mulEquivHaarChar b = (T.leviModulus C l.val : ℝ≥0)
  rw [← hc, mulEquivHaarChar_eq haar a]
  have hscale : (haar : Measure (C.unipotentRadical F)).map a =
      ((T.leviModulus C l.val : ℝ≥0)⁻¹) • haar :=
    by
      have ha : (a : C.unipotentRadical F → C.unipotentRadical F) =
          C.leviAction F l.val := by
        funext u
        apply Subtype.ext
        rfl
      rw [ha]
      exact Langlands.AllField.glBlockModulusHaar F T n C haar l.val
  have hs := mul_haarScalarFactor_smul
    (haar : Measure (C.unipotentRadical F)) haar
    (c := (T.leviModulus C l.val : ℝ≥0)⁻¹) (inv_ne_zero (Units.ne_zero _))
  rw! [hscale]
  rw [haarScalarFactor_self] at hs
  exact ((inv_mul_eq_one₀ (Units.ne_zero _)).mp hs).symm

/-- The actual correction character is unchanged on projection to the refined Levi. -/
theorem parabolicOrbitStagesCorrectionModulus_factor
    (R : BlockRefinement C)
    (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
    (l : parabolicOrbitStagesQuotient F B C w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    parabolicOrbitStagesCorrectionModulus F B C w l =
      parabolicOrbitStagesCorrectionModulus F B C w
        ((parabolicOrbitStagesRefinedEquiv F B C w R hR).symm
          (refinedLeviSection F C R
            (refinedLeviProjection F C R
              (parabolicOrbitStagesRefinedEquiv F B C w R hR l)))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let e := parabolicOrbitStagesRefinedEquivContinuous F B C w R hR
  let U := intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
    (permutation n F w)⁻¹
  have hU : IsClosed (U : Set (GeneralLinear n F)) :=
    General.isClosed_correctionSubgroup _ _ _
      (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F)
  let χ := parabolicOrbitStagesCorrectionModulus F B C w
  have hc : Continuous χ :=
    (Weil.continuous_of_open_kernel (HaarModulus.closedNormalizerCharacter U hU)
      (HaarModulus.isOpen_ker_closedNormalizerCharacter U hU)).comp
        (continuous_parabolicOrbitStagesCorrectionNormalizer F B C w)
  have hf := T.refinedPositiveCharacter_factor C R
    (χ.comp e.symm.toMonoidHom) (hc.comp e.symm.continuous) (e l)
  change χ (e.symm (e l)) =
    χ (e.symm (refinedLeviSection F C R
      (refinedLeviProjection F C R (e l)))) at hf
  rw [ContinuousMulEquiv.symm_apply_apply] at hf
  have he (q : parabolicOrbitStagesQuotient F B C w) :
      e q = parabolicOrbitStagesRefinedEquiv F B C w R hR q := by
    apply Subtype.ext
    rfl
  have hi (q : refinedParabolic F C R) :
      e.symm q = (parabolicOrbitStagesRefinedEquiv F B C w R hR).symm q := by
    apply Subtype.ext
    rfl
  rw [he, hi] at hf
  exact hf

end Langlands.LocalFieldData
