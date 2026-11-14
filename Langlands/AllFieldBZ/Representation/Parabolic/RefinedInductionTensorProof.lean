import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorMap
import Langlands.Representation.Parabolic.RefinedInductionTensorProof

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinedInductionTensorProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor
open Langlands.Parabolic.RefinedInductionTensor hiding BlockFunctions CanonicalInverse Comparison Factors RefinedFunctions blockInducingRepresentation blockRepresentations comparison_of_pointwiseMap_bijective coordinateInducingRepresentation coordinateInducingRepresentation_eq externalRepresentation inducedNormalizationEquiv inducingNormalizationEquiv inducingNormalizationEquiv_apply inducingRepresentation normalizedRefinedInducingRepresentation pointwiseMap pointwiseMap_bijective pointwiseMap_tprod_eval productInducing_eq refinedRepresentation
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  (A : Factors.{uF, uV} F T B S)

/-- The generic compact-quotient bijectivity result specializes to the actual
normalized refined pointwise map. -/
theorem pointwiseMap_bijective :
    Function.Bijective (pointwiseMap F T B S A) := by
  let := T.topology
  let : ∀ i : Fin B.length,
      NonarchimedeanGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearNonarchimedean (B.size i)
  let : ∀ i : Fin B.length,
      LocallyCompactSpace (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearLocallyCompactSpace (B.size i)
  let : ∀ i : Fin B.length,
      CompactSpace (Induction.LeftQuotient ((S i).parabolic F.Carrier)) :=
    fun i => parabolicQuotientCompact F T (S i)
  have hb := Induction.finiteProductTensorMap_bijective ℂ (Fin B.length)
    (fun i => GeneralLinear (B.size i) F.Carrier)
    (fun i => (S i).parabolic F.Carrier)
    (fun i => ↑(A i).obj) (blockInducingRepresentation F T B S A)
  exact (inducedNormalizationEquiv F T B S A).bijective.comp hb

/-- Bijectivity of the actual pointwise map constructs the requested equivalence
and its canonical inverse, with the orientation in the published statement. -/
theorem comparison_of_pointwiseMap_bijective
    (h : Function.Bijective (pointwiseMap F T B S A)) :
    Comparison F T B S A := by
  let := T.topology
  let E := (pointwiseMap F T B S A).ofBijective h
  refine ⟨⟨E.symm, ?_⟩⟩
  intro f g
  change Induction.eval _ _ (pointwiseMap F T B S A (PiTensorProduct.tprod ℂ f)) g = _
  exact pointwiseMap_tprod_eval F T B S A f g

end Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding ParabolicQuotientCompactClause RefinedInductionTensorTheorem UnipotentFiniteContainmentClause isCompact_integralRange parabolicQuotientCompact quotientMap_image_integralRange refinedInductionTensor
universe uF uV

/-- Normalized refined induction commutes with the finite external tensor
product, with the prescribed pointwise pure-tensor inverse. -/
theorem refinedInductionTensor : RefinedInductionTensorTheorem.{uF, uV} := by
  intro F T n B S A
  exact RefinedInductionTensor.comparison_of_pointwiseMap_bijective F T B S A
    (RefinedInductionTensor.pointwiseMap_bijective F T B S A)

end Langlands.AllFieldBZ.Parabolic
