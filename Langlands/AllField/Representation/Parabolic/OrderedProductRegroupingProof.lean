import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.AllField.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.AllField.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.AllField.Representation.Parabolic.RefinementCoordinatesNormalizationProof
import Langlands.AllField.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.AllField.Representation.Tensor.GLRefinement
/-! Ordered normalized product regrouping from the actual comparison isomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause OrderedProductRegrouping RefinedInductionTensorTheorem RefinementCoordinatesNormalizationTheorem isCompact_integralRange normalizedRefinementInductionTransitivity orderedProductRegrouping parabolicQuotientCompact quotientMap_image_integralRange refinedInductionTensor refinementCoordinatesNormalization
open Langlands.AllField.Parabolic

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Regroup normalized products along the prescribed ordered refinement, with
independent field and input carrier universes. -/
theorem orderedProductRegrouping :
    OrderedProductRegrouping.{uF,uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B D S e h hc σ
  let τ : ∀ j, ∀ k : Fin (S j).length,
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size k) F) :=
    fun j k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)
  let A : Langlands.AllField.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S :=
    fun j => FiniteTensor.externalSmoothObject (τ j)
  let flat := FiniteTensor.externalSmoothObject σ
  let pulled : SmoothRep.{0,uF,uV} ℂ (refinedLevi F D S) :=
    SmoothRep.of (flat.representation.comp
      (B.leviRefinementEquiv D S e h F).symm.toMonoidHom)
      (isSmooth_comp _ (B.leviRefinementEquivContinuous D S e h F).symm.continuous
        flat.isSmooth)
  let nested : SmoothRep.{0,uF,uV} ℂ (refinedLevi F D S) :=
    SmoothRep.of (Langlands.AllField.Parabolic.RefinedInductionTensor.inducingRepresentation F T D S A)
      (isSmooth_comp _ (refinedLeviEquivContinuous F D S).symm.continuous
        (FiniteTensor.externalSmoothObject A).isSmooth)
  let etensor := Langlands.AllField.FiniteTensor.glRefinementEquiv F T B D S e h σ
  let itensor : pulled ≅ nested := SmoothRep.mkIso etensor
  obtain ⟨ecoordinate, _, _⟩ :=
    (refinementCoordinatesNormalization.{uF,uV} F T n B D S e h hc).2.2
      _ flat.representation
  let icoordinate :
      (T.normalizedComposedInductionFunctor.{uF,uV} D S).obj pulled ≅
      (T.normalizedProductInductionFunctor.{uF,uV} B).obj σ :=
    SmoothRep.mkIso ecoordinate
  obtain ⟨istages, _, _⟩ := normalizedRefinementInductionTransitivity.{uF,uV}
    F T D S
  obtain ⟨eind, _⟩ := refinedInductionTensor.{uF,uV} F T n D S A
  let iind : (T.normalizedRefinedInductionFunctor.{uF,uV} D S).obj nested ≅
      FiniteTensor.externalSmoothObject (fun j =>
        (T.normalizedParabolicInductionFunctor.{uF,uV} (S j)).obj (A j)) :=
    SmoothRep.mkIso eind
  refine ⟨icoordinate.symm ≪≫
    (T.normalizedComposedInductionFunctor.{uF,uV} D S).mapIso itensor ≪≫
    (istages.app nested).symm ≪≫
    (T.normalizedParabolicInductionFunctor.{uF,max uF uV} D).mapIso iind⟩

end Langlands.AllField.Parabolic
