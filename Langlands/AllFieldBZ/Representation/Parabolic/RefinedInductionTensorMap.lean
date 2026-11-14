import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorNormalization
import Langlands.Representation.Parabolic.RefinedInductionTensorMap

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorMap`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinedInductionTensorMap` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor
open Langlands.Parabolic.RefinedInductionTensor hiding BlockFunctions CanonicalInverse Comparison Factors RefinedFunctions blockInducingRepresentation blockRepresentations coordinateInducingRepresentation coordinateInducingRepresentation_eq externalRepresentation inducedNormalizationEquiv inducingNormalizationEquiv inducingNormalizationEquiv_apply inducingRepresentation normalizedRefinedInducingRepresentation pointwiseMap pointwiseMap_tprod_eval productInducing_eq refinedRepresentation
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  (A : Factors.{uF, uV} F T B S)

/-- The literal product-subgroup inducing action is the actual normalized
refined inducing action. -/
theorem productInducing_eq :
    Induction.productInducing (fun i => (S i).parabolic F.Carrier)
      (blockInducingRepresentation F T B S A) =
      normalizedRefinedInducingRepresentation F T B S A := by
  calc
    _ = coordinateInducingRepresentation F T B S A := by
      ext q v
      rfl
    _ = _ := coordinateInducingRepresentation_eq F T B S A

/-- Normalization identifies the inducing actions by the identity on their
original tensor coefficient space. -/
def inducingNormalizationEquiv :
    (Induction.productInducing (fun i => (S i).parabolic F.Carrier)
      (blockInducingRepresentation F T B S A)).Equiv
      (normalizedRefinedInducingRepresentation F T B S A) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' q := by
    change Induction.productInducing (fun i => (S i).parabolic F.Carrier)
      (blockInducingRepresentation F T B S A) q =
        normalizedRefinedInducingRepresentation F T B S A q
    exact congrArg (fun ρ => ρ q) (productInducing_eq F T B S A)

@[simp]
theorem inducingNormalizationEquiv_apply
    (v : PiTensorProduct ℂ (fun i => ↑(A i).obj)) :
    inducingNormalizationEquiv F T B S A v = v := rfl

/-- Identity postcomposition transports actual smooth induced functions from
product covariance to the normalized refined covariance. -/
def inducedNormalizationEquiv :
    letI := T.topology
    letI : ∀ i : Fin B.length,
        IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
      fun i => T.generalLinearTopologicalGroup (B.size i)
    (Induction.smoothInduced (refinedParabolic F.Carrier B S)
      (Induction.productInducing (fun i => (S i).parabolic F.Carrier)
        (blockInducingRepresentation F T B S A))).Equiv
      (refinedRepresentation F T B S A) := by
  letI := T.topology
  letI : ∀ i : Fin B.length,
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  exact Induction.smoothInducedEquiv _ (inducingNormalizationEquiv F T B S A)

/-- The pointwise tensor map with the actual normalized refined target. -/
def pointwiseMap :
    (externalRepresentation F T B S A).IntertwiningMap
      (refinedRepresentation F T B S A) := by
  letI := T.topology
  letI : ∀ i : Fin B.length,
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  exact (inducedNormalizationEquiv F T B S A).toIntertwiningMap.comp
    (Induction.finiteProductTensorMap (fun i => (S i).parabolic F.Carrier)
      (blockInducingRepresentation F T B S A))

/-- The map has precisely the evaluation prescribed for the eventual inverse
in the published comparison statement. -/
@[simp]
theorem pointwiseMap_tprod_eval
    (f : ∀ i, BlockFunctions F T B S A i) (g : B.Levi F.Carrier) :
    letI := T.topology
    Induction.eval _ _ (pointwiseMap F T B S A (PiTensorProduct.tprod ℂ f)) g =
      PiTensorProduct.tprod ℂ (fun i => Induction.eval _ _ (f i) (g i)) := by
  let := T.topology
  let : ∀ i : Fin B.length,
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  change Induction.eval _ _
    (Induction.finiteProductTensorMap (fun i => (S i).parabolic F.Carrier)
      (blockInducingRepresentation F T B S A) (PiTensorProduct.tprod ℂ f)) g = _
  exact Induction.finiteProductTensorMap_tprod_eval _ _ f g

end Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor
