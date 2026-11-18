import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryFromLocalModels
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismSchemeRepresentatives
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonProof

/-! # Full relative Aut geometry from pinned label completeness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The exact general-base geometry follows from affine pinned classification,
local completeness of the full-lattice labels, and independent adjoint existence.
Natural local pinning is supplied by its published unconditional theorem. -/
theorem reductiveAutomorphismSchemeGeometry_of_pinnedLabelCompleteness
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hcomplete : ∀ M N : AffinePinnedModel.{u},
      AffinePinnedModel.OpenPinnedLabelCompleteness M N hAffine) :
    ReductiveAutomorphismSchemeGeometryStatement.{u} :=
  reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives
    (pinnedOuterIsomorphismChart_of_localCompleteness hAffine
      AffinePinnedModel.hasFppfLocalPinnedRepresentatives hcomplete)
    hAdj
    (affinePinnedAutomorphismRepresentatives_of_pinnedLabelCompleteness hAffine hAdj
      AffinePinnedModel.hasFppfLocalPinnedRepresentatives (fun M => hcomplete M M))

/-- Select the full general-base Aut scheme constructed from complete pinned
labels and an independently established adjoint-existence theorem. -/
def automorphismSchemeOfPinnedLabelCompleteness
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hcomplete : ∀ M N : AffinePinnedModel.{u},
      AffinePinnedModel.OpenPinnedLabelCompleteness M N hAffine)
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G) :
    GroupIsomorphismScheme G G :=
  Classical.choose
    (reductiveAutomorphismSchemeGeometry_of_pinnedLabelCompleteness hAffine hAdj hcomplete S G hG)

end Langlands.GroupScheme
