import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedRefinementInduction
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.AllFieldBZ.Representation.Tensor.GLRefinement
import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction

/-!
# All-field port of `Langlands.Representation.Parabolic.OrderedRefinementTensorInduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.OrderedRefinementTensorInduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause ParabolicQuotientCompactClause RefinedInductionTensorTheorem RefinementCoordinatesNormalizationTheorem UnipotentFiniteContainmentClause isCompact_integralRange normalizedRefinementInductionTransitivity orderedRefinementInductionEquiv orderedRefinementIteratedInduced orderedRefinementTensorFactors orderedRefinementTensorInductionEquiv parabolicQuotientCompact quotientMap_image_integralRange refinedInductionTensor refinementCoordinatesNormalization
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))

/-- The regrouped factors use the actual rank equality on every block. -/
def orderedRefinementTensorFactors :
    letI := T.topology
    (∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) →
      RefinedInductionTensor.Factors.{uF,uV} F T D S :=
  letI := T.topology
  fun σ j => FiniteTensor.externalSmoothObject (fun k =>
    ((hs ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩) :
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size k) F.Carrier)))

variable (hc : ∀ i k x, D.index i ((S i).index k x) =
  B.index (e ⟨i,k⟩) (Fin.cast (hs ⟨i,k⟩) x))

/-- Ordinary normalized induction of the original block factors is equivalent
 to outer induction of the actual normalized products in each refined block. -/
def orderedRefinementTensorInductionEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      Representation.Equiv
        (T.normalizedProductInduced B (fun i => (σ i).representation))
        (T.normalizedParabolicInduced D
          (RefinedInductionTensor.externalRepresentation F T D S
            (orderedRefinementTensorFactors F T B D S e hs σ))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup D
  intro σ
  let A := orderedRefinementTensorFactors F T B D S e hs σ
  let E₀ := FiniteTensor.glRefinementEquiv F T B D S e hs σ
  let E₁ : Representation.Equiv
      (T.normalizedRefinedInduced D S
        ((B.blockTensor (fun i => (σ i).representation)).comp
          (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom))
      (RefinedInductionTensor.refinedRepresentation F T D S A) :=
    Induction.smoothInducedEquiv (refinedParabolic F.Carrier D S)
      (twistEquiv (T.refinedParabolicHalfModulus D S)
        (Representation.Equiv.mk E₀.toLinearEquiv
          (fun q => E₀.isIntertwining' (refinedLeviProjection F.Carrier D S q))))
  let E₂ := (refinedInductionTensor.{uF,uV} F T n D S A).some.val
  have hσ : IsSmooth (B.blockTensor (fun i => (σ i).representation)) :=
    FiniteTensor.isSmooth_external _ (fun i => (σ i).property)
  exact (orderedRefinementInductionEquiv F T B D S e hs hc
      (B.blockTensor (fun i => (σ i).representation)) hσ).symm.trans
    (T.normalizedParabolicInducedEquiv D (E₁.trans E₂))

end Langlands.AllFieldBZ.Parabolic
