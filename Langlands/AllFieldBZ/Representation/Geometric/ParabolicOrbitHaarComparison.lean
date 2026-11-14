import Langlands.AllFieldBZ.Group.GL.BlockModulusHaarProof
import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitNestedAction
import Langlands.AllFieldBZ.Representation.Geometric.RefinedPositiveCharacter
import Langlands.Representation.Geometric.ParabolicOrbitHaarComparison

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitHaarComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitHaarComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
open Langlands.Induction
open MeasureTheory
open MeasureTheory.Measure
open scoped NNReal
universe uF

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable [TopologicalSpace F] [IsTopologicalRing F]

section Haar
variable [T2Space F] [LocallyCompactSpace (GeneralLinear n F)]

local instance radicalLocallyCompact :
    LocallyCompactSpace (C.unipotentSubgroup F) :=
  (C.isClosed_unipotentSubgroup F).locallyCompactSpace

local instance correctionLocallyCompact :
    LocallyCompactSpace
      (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹) :=
  (General.isClosed_correctionSubgroup _ _ _
    (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F)).locallyCompactSpace

local instance nestedKernelLocallyCompact :
    LocallyCompactSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  (parabolicOrbitNestedKernelAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance nestedIntersectionLocallyCompact :
    LocallyCompactSpace (parabolicOrbitNestedIntersection F B C w) :=
  (parabolicOrbitNestedIntersectionAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance subgroupMeasurableSpace {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace H := borel H

local instance subgroupBorelSpace {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : BorelSpace H := ⟨rfl⟩

end Haar
end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
open MeasureTheory
open MeasureTheory.Measure
open scoped NNReal
universe uF

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- The actual ambient radical Haar character is the explicit block modulus. -/
theorem parabolicOrbitStagesRadicalModulus
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    HaarModulus.closedNormalizerCharacter (C.unipotentSubgroup F.Carrier)
        (C.isClosed_unipotentSubgroup F.Carrier)
        (parabolicOrbitStagesRadicalNormalizer F.Carrier B C w l) =
      T.leviModulus C l.val := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace (C.unipotentSubgroup F.Carrier) :=
    (C.isClosed_unipotentSubgroup F.Carrier).locallyCompactSpace
  let : MeasurableSpace (C.unipotentRadical F.Carrier) := borel _
  let : BorelSpace (C.unipotentRadical F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (C.unipotentSubgroup F.Carrier) := borel _
  let : BorelSpace (C.unipotentSubgroup F.Carrier) := ⟨rfl⟩
  let a := HaarModulus.normalizerConj (C.unipotentRadical F.Carrier)
    ⟨C.leviInParabolic F.Carrier l.val, by
      rw [Subgroup.normalizer_eq_top]
      trivial⟩
  let b := HaarModulus.normalizerConj (C.unipotentSubgroup F.Carrier)
    (parabolicOrbitStagesRadicalNormalizer F.Carrier B C w l)
  have hc := haarChar_eq_of_conjugacy (C.unipotentRadicalAmbientEquiv F.Carrier)
    a b (by intro u; apply Subtype.ext; rfl)
  apply Units.ext
  change mulEquivHaarChar b = (T.leviModulus C l.val : ℝ≥0)
  rw [← hc, mulEquivHaarChar_eq haar a]
  have hscale : (haar : Measure (C.unipotentRadical F.Carrier)).map a =
      ((T.leviModulus C l.val : ℝ≥0)⁻¹) • haar :=
    by
      have ha : (a : C.unipotentRadical F.Carrier → C.unipotentRadical F.Carrier) =
          C.leviAction F.Carrier l.val := by
        funext u
        apply Subtype.ext
        rfl
      rw [ha]
      exact glBlockModulusHaar F T n C haar l.val
  have hs := mul_haarScalarFactor_smul
    (haar : Measure (C.unipotentRadical F.Carrier)) haar
    (c := (T.leviModulus C l.val : ℝ≥0)⁻¹) (inv_ne_zero (Units.ne_zero _))
  rw! [hscale]
  rw [haarScalarFactor_self] at hs
  exact ((inv_mul_eq_one₀ (Units.ne_zero _)).mp hs).symm

/-- The actual correction character is unchanged on projection to the refined Levi. -/
theorem parabolicOrbitStagesCorrectionModulus_factor
    (R : BlockRefinement C)
    (hR : IsIntersectionRefinement (F := F.Carrier) C B w⁻¹ R)
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    parabolicOrbitStagesCorrectionModulus F.Carrier B C w l =
      parabolicOrbitStagesCorrectionModulus F.Carrier B C w
        ((parabolicOrbitStagesRefinedEquiv F.Carrier B C w R hR).symm
          (refinedLeviSection F.Carrier C R
            (refinedLeviProjection F.Carrier C R
              (parabolicOrbitStagesRefinedEquiv F.Carrier B C w R hR l)))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let e := parabolicOrbitStagesRefinedEquivContinuous F.Carrier B C w R hR
  let U := intersectionSource (C.unipotentSubgroup F.Carrier) (B.parabolic F.Carrier)
    (permutation n F.Carrier w)⁻¹
  have hU : IsClosed (U : Set (GeneralLinear n F.Carrier)) :=
    General.isClosed_correctionSubgroup _ _ _
      (C.isClosed_unipotentSubgroup F.Carrier) (B.isClosed_parabolic F.Carrier)
  let χ := parabolicOrbitStagesCorrectionModulus F.Carrier B C w
  have hc : Continuous χ :=
    (Weil.continuous_of_open_kernel (HaarModulus.closedNormalizerCharacter U hU)
      (HaarModulus.isOpen_ker_closedNormalizerCharacter U hU)).comp
        (continuous_parabolicOrbitStagesCorrectionNormalizer F.Carrier B C w)
  have hf := T.refinedPositiveCharacter_factor C R
    (χ.comp e.symm.toMonoidHom) (hc.comp e.symm.continuous) (e l)
  change χ (e.symm (e l)) =
    χ (e.symm (refinedLeviSection F.Carrier C R
      (refinedLeviProjection F.Carrier C R (e l)))) at hf
  rw [ContinuousMulEquiv.symm_apply_apply] at hf
  have he (q : parabolicOrbitStagesQuotient F.Carrier B C w) :
      e q = parabolicOrbitStagesRefinedEquiv F.Carrier B C w R hR q := by
    apply Subtype.ext
    rfl
  have hi (q : refinedParabolic F.Carrier C R) :
      e.symm q = (parabolicOrbitStagesRefinedEquiv F.Carrier B C w R hR).symm q := by
    apply Subtype.ext
    rfl
  rw [he, hi] at hf
  exact hf

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
