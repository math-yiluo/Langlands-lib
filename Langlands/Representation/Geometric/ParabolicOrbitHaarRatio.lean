import Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
import Langlands.Representation.Induction.SplitKernelEquivariant

/-! The actual orbit Haar ratio agrees with the generic split-kernel integral. -/

noncomputable section
namespace Langlands.Geometric
open GeneralLinear Induction MeasureTheory MeasureTheory.Measure
open scoped NNReal
universe uF
variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} [LocallyCompactSpace (GeneralLinear n F)]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

local instance : LocallyCompactSpace (C.unipotentSubgroup F) :=
  (C.isClosed_unipotentSubgroup F).locallyCompactSpace
local instance : LocallyCompactSpace
    (intersectionSource (C.unipotentSubgroup F) (B.parabolic F) (permutation n F w)⁻¹) :=
  (General.isClosed_correctionSubgroup _ _ _
    (C.isClosed_unipotentSubgroup F) (B.isClosed_parabolic F)).locallyCompactSpace
local instance : LocallyCompactSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  (parabolicOrbitNestedKernelAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : LocallyCompactSpace (parabolicOrbitNestedIntersection F B C w) :=
  (parabolicOrbitNestedIntersectionAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) :
    MeasurableSpace H := borel H
local instance {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) :
    BorelSpace H := ⟨rfl⟩

/-- The restricted nested inverse conjugation is ambient inverse conjugation. -/
theorem parabolicOrbitNestedIntersectionAmbientEquiv_conjugation
    (l : parabolicOrbitStagesQuotient F B C w)
    (i : parabolicOrbitNestedIntersection F B C w) :
    parabolicOrbitNestedIntersectionAmbientEquiv F B C w
        (splitKernelIntersectionConjugation (parabolicOrbitStagesRetraction F B C w)
          ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
          (parabolicOrbitNestedStabilizer F B C w)
          (parabolicOrbitNestedSection_mem F B C w) l i) =
      HaarModulus.normalizerConj
        (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
          (permutation n F w)⁻¹)
        (parabolicOrbitStagesCorrectionNormalizer F B C w l)⁻¹
        (parabolicOrbitNestedIntersectionAmbientEquiv F B C w i) := by
  apply Subtype.ext
  change (C.leviEmbedding F l.val)⁻¹ * i.val.val.val.val *
      ((C.leviEmbedding F l.val)⁻¹)⁻¹ =
    (C.leviEmbedding F l.val)⁻¹ * i.val.val.val.val *
      ((C.leviEmbedding F l.val)⁻¹)⁻¹
  rfl

theorem parabolicOrbitNestedIntersection_haarChar
    (l : parabolicOrbitStagesQuotient F B C w) :
    mulEquivHaarChar
        (splitKernelIntersectionConjugation (parabolicOrbitStagesRetraction F B C w)
          ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
          (parabolicOrbitNestedStabilizer F B C w)
          (parabolicOrbitNestedSection_mem F B C w) l) =
      ((HaarModulus.normalizerCharacter
        (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
          (permutation n F w)⁻¹)
        (parabolicOrbitStagesCorrectionNormalizer F B C w l) : ℝ≥0)⁻¹) := by
  rw [haarChar_eq_of_conjugacy (parabolicOrbitNestedIntersectionAmbientEquiv F B C w)
    _ _ (parabolicOrbitNestedIntersectionAmbientEquiv_conjugation F B C w l)]
  change (HaarModulus.normalizerCharacter
    (intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
      (permutation n F w)⁻¹)
    (parabolicOrbitStagesCorrectionNormalizer F B C w l)⁻¹ : ℝ≥0) = _
  rw [map_inv, Units.val_inv_eq_inv_val]


/-- The quotient integral's two nested Haar factors are the ambient ratio. -/
theorem parabolicOrbitStagesHaarRatio_eq_splitKernelHaarRatio :
    parabolicOrbitStagesHaarRatio F B C w =
      splitKernelHaarRatio (parabolicOrbitStagesRetraction F B C w)
        ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
        (parabolicOrbitNestedStabilizer F B C w)
        (parabolicOrbitNestedSection_mem F B C w)
        ((isClosed_parabolicOrbitStabilizer F B C w).preimage continuous_subtype_val) := by
  apply MonoidHom.ext
  intro l
  apply Units.ext
  change _ = mulEquivHaarChar
      (splitKernelIntersectionConjugation (parabolicOrbitStagesRetraction F B C w)
        ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
        (parabolicOrbitNestedStabilizer F B C w)
        (parabolicOrbitNestedSection_mem F B C w) l) /
    mulEquivHaarChar
      (splitKernelConjugation (parabolicOrbitStagesRetraction F B C w)
        ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w)) l)
  rw [parabolicOrbitNestedIntersection_haarChar, parabolicOrbitNestedKernel_haarChar]
  simp only [parabolicOrbitStagesHaarRatio, MonoidHom.div_apply, MonoidHom.comp_apply,
    Units.val_div_eq_div_val, inv_div_inv]


end Langlands.Geometric
