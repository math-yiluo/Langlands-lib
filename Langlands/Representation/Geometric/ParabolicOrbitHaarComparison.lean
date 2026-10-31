import Langlands.Representation.Geometric.ParabolicOrbitHaarTransport
import Langlands.Representation.Geometric.ParabolicOrbitNestedAction
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Representation.Geometric.RefinedPositiveCharacter
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Group.GL.CompactOpen

/-! Identification of the actual nested Haar ratio with ambient characters. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uF

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The full intermediate section is the actual ambient intersection of the
 target Levi with the conjugated source parabolic. -/
def parabolicOrbitStagesAmbient :
    parabolicOrbitStagesQuotient F B C w →*
      General.intersectionIn (C.leviSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹ where
  toFun l := ⟨C.leviEquiv F l.val, parabolicOrbitStages_section_mem F B C w l⟩
  map_one' := Subtype.ext ((C.leviEquiv F).map_one)
  map_mul' x y := Subtype.ext ((C.leviEquiv F).map_mul x.val y.val)

/-- The full intermediate group acts by the actual ambient radical normalizer. -/
def parabolicOrbitStagesRadicalNormalizer :
    parabolicOrbitStagesQuotient F B C w →*
      Subgroup.normalizer (C.unipotentSubgroup F : Set (GeneralLinear n F)) :=
  (General.intersectionToRadicalNormalizer (C.leviSubgroup F) (B.parabolic F)
    (C.unipotentSubgroup F) (permutation n F w)⁻¹
    (C.leviSubgroup_le_normalizer_unipotentSubgroup F)).comp
      (parabolicOrbitStagesAmbient F B C w)

/-- The full intermediate group acts on the literal correction subgroup. -/
def parabolicOrbitStagesCorrectionNormalizer :
    parabolicOrbitStagesQuotient F B C w →*
      Subgroup.normalizer (intersectionSource (C.unipotentSubgroup F)
        (B.parabolic F) (permutation n F w)⁻¹ : Set (GeneralLinear n F)) :=
  (General.intersectionToCorrectionNormalizer (C.leviSubgroup F) (B.parabolic F)
    (C.unipotentSubgroup F) (B.parabolic F) (permutation n F w)⁻¹
    (C.leviSubgroup_le_normalizer_unipotentSubgroup F) (B.parabolic F).le_normalizer).comp
      (parabolicOrbitStagesAmbient F B C w)

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- The actual nested inverse conjugation is ambient inverse conjugation. -/
theorem parabolicOrbitNestedKernelAmbientEquiv_conjugation
    (l : parabolicOrbitStagesQuotient F B C w)
    (u : (parabolicOrbitStagesRetraction F B C w).ker) :
    parabolicOrbitNestedKernelAmbientEquiv F B C w
        (splitKernelConjugation (parabolicOrbitStagesRetraction F B C w)
          ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w)) l u) =
      HaarModulus.normalizerConj (C.unipotentSubgroup F)
        (parabolicOrbitStagesRadicalNormalizer F B C w l)⁻¹
        (parabolicOrbitNestedKernelAmbientEquiv F B C w u) := by
  apply Subtype.ext
  change (C.leviEmbedding F l.val)⁻¹ * u.val.val.val *
      ((C.leviEmbedding F l.val)⁻¹)⁻¹ =
    (C.leviEmbedding F l.val)⁻¹ * u.val.val.val *
      ((C.leviEmbedding F l.val)⁻¹)⁻¹
  rfl


omit [IsTopologicalRing F] in
theorem continuous_parabolicOrbitStagesRadicalNormalizer :
    Continuous (parabolicOrbitStagesRadicalNormalizer F B C w) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun l : parabolicOrbitStagesQuotient F B C w =>
    C.leviEmbedding F l.val)
  exact (C.leviEmbeddingContinuous F).continuous.comp continuous_subtype_val

omit [IsTopologicalRing F] in
theorem continuous_parabolicOrbitStagesCorrectionNormalizer :
    Continuous (parabolicOrbitStagesCorrectionNormalizer F B C w) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun l : parabolicOrbitStagesQuotient F B C w =>
    C.leviEmbedding F l.val)
  exact (C.leviEmbeddingContinuous F).continuous.comp continuous_subtype_val

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

/-- The full intermediate group's actual correction-subgroup Haar modulus. -/
def parabolicOrbitStagesCorrectionModulus :
    parabolicOrbitStagesQuotient F B C w →* ℝ≥0ˣ :=
  (HaarModulus.closedNormalizerCharacter
    (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
      (permutation n F w)⁻¹)
    (General.isClosed_correctionSubgroup _ _ _
      (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F))).comp
        (parabolicOrbitStagesCorrectionNormalizer F B C w)

/-- The actual forward-precomposition ratio on the full intermediate group. -/
def parabolicOrbitStagesHaarRatio : parabolicOrbitStagesQuotient F B C w →* ℝ≥0ˣ :=
  (HaarModulus.normalizerCharacter (C.unipotentSubgroup F)).comp
      (parabolicOrbitStagesRadicalNormalizer F B C w) /
    (HaarModulus.normalizerCharacter
      (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹)).comp
      (parabolicOrbitStagesCorrectionNormalizer F B C w)

theorem parabolicOrbitNestedKernel_haarChar
    (l : parabolicOrbitStagesQuotient F B C w) :
    mulEquivHaarChar
        (splitKernelConjugation (parabolicOrbitStagesRetraction F B C w)
          ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w)) l) =
      ((HaarModulus.normalizerCharacter (C.unipotentSubgroup F)
        (parabolicOrbitStagesRadicalNormalizer F B C w l) : ℝ≥0)⁻¹) := by
  rw [haarChar_eq_of_conjugacy (parabolicOrbitNestedKernelAmbientEquiv F B C w)
    _ _ (parabolicOrbitNestedKernelAmbientEquiv_conjugation F B C w l)]
  change (HaarModulus.normalizerCharacter (C.unipotentSubgroup F)
    (parabolicOrbitStagesRadicalNormalizer F B C w l)⁻¹ : ℝ≥0) = _
  rw [map_inv, Units.val_inv_eq_inv_val]


end Haar

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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
      exact glBlockModulusHaar p F T n C haar l.val
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

end Langlands.PadicField.TopologicalData
