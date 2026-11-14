import Langlands.Representation.Geometric.ParabolicOrbitNormalization
import Langlands.AllField.Representation.Geometric.IntersectionLeviModulusBalance
import Langlands.AllField.Representation.Geometric.ParabolicOrbitHaarComparison
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! Cancellation of the actual orbit integration and normalization characters. -/

noncomputable section

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric
open scoped NNReal

universe uF

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F) B C w.val S)
  (hR : IsIntersectionRefinement (F := F) C B w.val⁻¹ R)

/-- On the full intermediate group, the two source half moduli and the target
half modulus equal the refined target half modulus times the actual correction. -/
theorem parabolicOrbitSectionCharacter_halfBalance
    (l : parabolicOrbitStagesQuotient F B C w.val) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    T.parabolicOrbitSectionCharacter B C w.val S R hS hR l *
        T.leviHalfModulus C l.val =
      T.refinedParabolicHalfModulus C R
          (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l) *
        Jacquet.complexCharacter
          (parabolicOrbitStagesCorrectionModulus F B C w.val) l := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let t := parabolicOrbitTargetLeviProjection F B C w.val R hR l
  let m := parabolicOrbitSourceLeviCoordinate F B C w.val R hR l
  let j : General.intersectionIn (C.leviSubgroup F)
      (B.leviSubgroup F) (permutation n F w.val)⁻¹ :=
    ⟨C.leviEquiv F t.val, by
      have ht := t.property
      change permutation n F w.val⁻¹ * C.leviEmbedding F t.val *
        (permutation n F w.val⁻¹)⁻¹ ∈ B.leviSubgroup F at ht
      change (permutation n F w.val)⁻¹ * C.leviEmbedding F t.val *
        ((permutation n F w.val)⁻¹)⁻¹ ∈ B.leviSubgroup F
      simpa only [map_inv] using ht⟩
  have hmt : intersectionLeviConjugation F B C w.val m = t :=
    (intersectionLeviConjugation F B C w.val).apply_symm_apply t
  have hj : j.val.val = C.leviEmbedding F
      (intersectionLeviConjugation F B C w.val m).val := by
    rw [hmt]
    rfl
  have hb := intersectionLeviHalfModulusBalance_sourceLevi F T n B C w S R
    hS.2.1 hR.2.1 m j hj
  rw [hmt] at hb
  let l₀ := (parabolicOrbitStagesRefinedEquiv F B C w.val R hR).symm
    (refinedLeviSection F C R
      (refinedLeviProjection F C R
        (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l)))
  have hc := T.parabolicOrbitStagesCorrectionModulus_factor B C w.val R hR l
  change parabolicOrbitStagesCorrectionModulus F B C w.val l =
    parabolicOrbitStagesCorrectionModulus F B C w.val l₀ at hc
  have hn :
      General.intersectionToCorrectionNormalizer (C.leviSubgroup F)
        (B.leviSubgroup F) (C.unipotentSubgroup F)
        (B.parabolic F) (permutation n F w.val)⁻¹
        (C.leviSubgroup_le_normalizer_unipotentSubgroup F)
        (fun x hx => (B.parabolic F).le_normalizer
          (B.leviAsParabolic F ⟨x, hx⟩).property) j =
      parabolicOrbitStagesCorrectionNormalizer F B C w.val l₀ := by
    apply Subtype.ext
    rfl
  let U := intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
    (permutation n F w.val)⁻¹
  have hU : IsClosed (U : Set (GeneralLinear n F)) :=
    General.isClosed_correctionSubgroup _ _ _
      (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F)
  have he :
      Jacquet.complexCharacter
        (General.intersectionCorrectionModulus (C.leviSubgroup F)
          (B.leviSubgroup F) (C.unipotentSubgroup F)
          (B.parabolic F) (permutation n F w.val)⁻¹
          (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F)
          (C.leviSubgroup_le_normalizer_unipotentSubgroup F)
          (fun x hx => (B.parabolic F).le_normalizer
            (B.leviAsParabolic F ⟨x, hx⟩).property)) j =
        Jacquet.complexCharacter
          (parabolicOrbitStagesCorrectionModulus F B C w.val) l := by
    unfold Jacquet.complexCharacter
    simp only [MonoidHom.comp_apply]
    congr 1
    rw [hc]
    change HaarModulus.closedNormalizerCharacter U hU _ =
      HaarModulus.closedNormalizerCharacter U hU _
    rw [hn]
  rw [he] at hb
  have hhalf := T.refinedOuterHalfModulus_projection C R
    (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l)
  change T.leviHalfModulus C t.val = T.leviHalfModulus C l.val at hhalf
  rw [hhalf] at hb
  change T.leviHalfModulus B m.val *
      T.refinedLeviHalfModulus B S (MulEquiv.subgroupCongr hS.2.1 m) *
      T.leviHalfModulus C l.val = _
  rw [mul_right_comm] at hb
  exact hb

/-- The actual forward integration ratio cancels all three normalizing factors. -/
theorem parabolicOrbitNormalization_cancel
    (l : parabolicOrbitStagesQuotient F B C w.val) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    Jacquet.inverseHalfCharacter (T.leviModulus C) l.val *
        Jacquet.complexCharacter
          (parabolicOrbitStagesHaarRatio F B C w.val) l *
        T.parabolicOrbitSectionCharacter B C w.val S R hS hR l =
      T.refinedParabolicHalfModulus C R
        (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  have hr :
      Jacquet.complexCharacter
          (parabolicOrbitStagesHaarRatio F B C w.val) l =
        T.leviHalfModulus C l.val ^ 2 /
          Jacquet.complexCharacter
            (parabolicOrbitStagesCorrectionModulus F B C w.val) l := by
    rw [T.leviHalfModulus_sq]
    unfold Jacquet.complexCharacter parabolicOrbitStagesHaarRatio
      parabolicOrbitStagesCorrectionModulus
    simp only [MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
    rw [← T.parabolicOrbitStagesRadicalModulus B C w.val l]
    rfl
  rw [hr]
  have hb := T.parabolicOrbitSectionCharacter_halfBalance B C w S R hS hR l
  let h := T.leviHalfModulus C l.val
  let e := Jacquet.complexCharacter
    (parabolicOrbitStagesCorrectionModulus F B C w.val) l
  let k := T.parabolicOrbitSectionCharacter B C w.val S R hS hR l
  let r := T.refinedParabolicHalfModulus C R
    (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l)
  change k * h = r * e at hb
  change h⁻¹ * (h ^ 2 / e) * k = r
  calc
    h⁻¹ * (h ^ 2 / e) * k = h * e⁻¹ * k := by
      simp only [pow_two, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = (k * h) / e := by
      rw [mul_right_comm, mul_comm h k, div_eq_mul_inv]
    _ = r := by rw [hb, mul_div_cancel_right]

end Langlands.LocalFieldData
