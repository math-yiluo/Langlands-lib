import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.CompactCoefficient.SelectedProjector

/-!
# All-field port of `Langlands.Representation.CompactCoefficient.SelectedProjector`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CompactCoefficient.SelectedProjector` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CompactCoefficientClass
open Langlands.CompactCoefficientClass
universe uG uH uC uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Selected
variable (t : Finset (CompactCoefficientClass.{uG, uC} G))
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ c : t, IsCompl (isotypicSubrepresentation c.val A).toSubmodule
      (annihilatorSubrepresentation c.val A).toSubmodule)

private theorem _root_.Langlands.CompactCoefficientClass.selected_components_orthogonal (c d : t) (hcd : c ≠ d) (v : A) :
    isotypicProjectorOfIsCompl c.val (h c)
      (isotypicProjectorOfIsCompl d.val (h d) v) = 0 := by
  have hdc : d.val ≠ c.val := fun heq => hcd (Subtype.ext heq.symm)
  exact congrArg (fun f : A.representation.IntertwiningMap A.representation => f v)
    (comp_eq_zero_of_isotypic_range_annihilator_ker hdc
      (isotypicProjectorOfIsCompl d.val (h d))
      (isotypicProjectorOfIsCompl c.val (h c))
      (isotypicProjectorOfIsCompl_range d.val (h d)).le
      (isotypicProjectorOfIsCompl_ker c.val (h c)).symm.le)

private theorem _root_.Langlands.CompactCoefficientClass.selected_components_idempotent (c : t) (v : A) :
    isotypicProjectorOfIsCompl c.val (h c)
      (isotypicProjectorOfIsCompl c.val (h c) v) =
      isotypicProjectorOfIsCompl c.val (h c) v := by
  exact congrArg (fun f : A →ₗ[ℂ] A => f v)
    (isotypicProjectorOfIsCompl_idempotent c.val (h c))

end Selected
section Ambient
variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (t : Finset (CompactCoefficientClass.{uG, uC} N))
    (ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ c : t,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule)

end Ambient
end Langlands.AllFieldBZ.CompactCoefficientClass
