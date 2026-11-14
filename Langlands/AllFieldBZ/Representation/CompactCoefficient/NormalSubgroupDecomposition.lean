import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition

/-!
# All-field port of `Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
universe uG uV

namespace SmoothRep
open Langlands.SmoothRep
variable {G : Type uG} [Group G] [TopologicalSpace G]

end SmoothRep
namespace CompactCoefficientClass
open Langlands.CompactCoefficientClass
open CategoryTheory
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]
  [NonarchimedeanGroup N] [WeaklyLocallyCompactSpace N]
  (hsplit : ∀ (c : CompactCoefficientClass.{uG, uV} N)
    (D : SmoothRep.{0, uG, uV} ℂ N),
    IsCompl (isotypicSubrepresentation c D).toSubmodule
      (annihilatorSubrepresentation c D).toSubmodule)
  (hstrata : ∀ K : OpenSubgroup N, IsCompact (K : Set N) →
    (fixedStratum.{uG, uV} K.toSubgroup).Finite)

omit [IsTopologicalGroup G] [N.Normal] [NonarchimedeanGroup N]
  [WeaklyLocallyCompactSpace N] in
private theorem _root_.Langlands.CompactCoefficientClass.components_orthogonal (D : SmoothRep.{0, uG, uV} ℂ N)
    (c d : CompactCoefficientClass.{uG, uV} N) (hcd : c ≠ d) (v : D) :
    isotypicProjectorOfIsCompl c (hsplit c D)
      (isotypicProjectorOfIsCompl d (hsplit d D) v) = 0 :=
  congrArg (fun f : D.representation.IntertwiningMap D.representation => f v)
    (isotypicProjectorFamilyOfIsCompl_orthogonal hsplit hcd.symm D)

end CompactCoefficientClass
end Langlands.AllFieldBZ
