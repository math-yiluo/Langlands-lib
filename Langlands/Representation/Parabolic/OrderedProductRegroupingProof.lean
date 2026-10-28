import Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Tensor.GLRefinement

/-! Ordered normalized product regrouping from the actual comparison isomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.Parabolic

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Regroup normalized products along the prescribed ordered refinement, with
independent field and input carrier universes. -/
theorem orderedProductRegrouping :
    OrderedProductRegrouping.{uF,uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B D S e h hc σ
  let τ : ∀ j, ∀ k : Fin (S j).length,
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size k) F.Carrier) :=
    fun j k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)
  let A : RefinedInductionTensor.Factors.{uF,uV} F T D S :=
    fun j => FiniteTensor.externalSmoothObject (τ j)
  let flat := FiniteTensor.externalSmoothObject σ
  let pulled : SmoothRep.{0,uF,uV} ℂ (refinedLevi F.Carrier D S) :=
    SmoothRep.of (flat.representation.comp
      (B.leviRefinementEquiv D S e h F.Carrier).symm.toMonoidHom)
      (isSmooth_comp _ (B.leviRefinementEquivContinuous D S e h F.Carrier).symm.continuous
        flat.isSmooth)
  let nested : SmoothRep.{0,uF,uV} ℂ (refinedLevi F.Carrier D S) :=
    SmoothRep.of (RefinedInductionTensor.inducingRepresentation F T D S A)
      (isSmooth_comp _ (refinedLeviEquivContinuous F.Carrier D S).symm.continuous
        (FiniteTensor.externalSmoothObject A).isSmooth)
  let etensor := FiniteTensor.glRefinementEquiv F T B D S e h σ
  let itensor : pulled ≅ nested := SmoothRep.mkIso etensor
  obtain ⟨ecoordinate, _, _⟩ :=
    (refinementCoordinatesNormalization.{uF,uV} p F T n B D S e h hc).2.2
      _ flat.representation
  let icoordinate :
      (T.normalizedComposedInductionFunctor.{uF,uV} D S).obj pulled ≅
      (T.normalizedProductInductionFunctor.{uF,uV} B).obj σ :=
    SmoothRep.mkIso ecoordinate
  obtain ⟨istages, _, _⟩ := normalizedRefinementInductionTransitivity.{uF,uV}
    F T D S
  obtain ⟨eind, _⟩ := refinedInductionTensor.{uF,uV} p F T n D S A
  let iind : (T.normalizedRefinedInductionFunctor.{uF,uV} D S).obj nested ≅
      FiniteTensor.externalSmoothObject (fun j =>
        (T.normalizedParabolicInductionFunctor.{uF,uV} (S j)).obj (A j)) :=
    SmoothRep.mkIso eind
  refine ⟨icoordinate.symm ≪≫
    (T.normalizedComposedInductionFunctor.{uF,uV} D S).mapIso itensor ≪≫
    (istages.app nested).symm ≪≫
    (T.normalizedParabolicInductionFunctor.{uF,max uF uV} D).mapIso iind⟩

end Langlands.Parabolic
