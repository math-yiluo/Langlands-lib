import Langlands.GroupScheme.Reductive.PinnedComparisonLabelDescent
import Langlands.GroupScheme.Reductive.PinnedComparisonLocalLabels

/-! # Constant pinned charts from the exact affine and normalization theorems -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffinePinnedModel

/-- Exact affine pinned classification proves open completeness of the full labels. -/
theorem openPinnedLabelCompleteness
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (M N : AffinePinnedModel.{u}) : OpenPinnedLabelCompleteness M N hAffine := by
  intro T f g e he x
  exact exists_open_comparisonLabel hAffine e he x

/-- The representation-free constant family together with its all-test adjoint
orbit classification, for arbitrary supplied full-centre quotients. -/
def pinnedComparisonChart
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : HasFppfLocalPinnedRepresentatives.{u})
    (M N : AffinePinnedModel.{u}) {S : Scheme.{u}}
    (f : S ⟶ M.base) (g : S ⟶ N.base)
    {A : GroupScheme S} {q : M.groupOver f ⟶ A} (hq : IsRelativeAdjointQuotient q) :
    { E : LocalGroupIso (M.groupOver f) (N.groupOver g)
        (GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N)) //
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) ×
            (T ⟶ GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N)) =>
          (E.refine z.2).twist hq.innerAction z.1⁻¹) } :=
  ⟨constantPinnedFamily M N hAffine f g,
    constantPinnedFamily_orbit_bijective M N hAffine f g
      (openPinnedLabelCompleteness hAffine M N) hlocal hq⟩

end Langlands.GroupScheme.AffinePinnedModel

namespace Langlands.GroupScheme

/-- The unchanged exact chart statement follows from the two independently
owned pinned affine and natural-normalization existence theorems. -/
theorem pinnedOuterIsomorphismChart_of_pinnedTheorems
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : AffinePinnedModel.HasFppfLocalPinnedRepresentatives.{u}) :
    PinnedOuterIsomorphismChartStatement.{u} :=
  pinnedOuterIsomorphismChart_of_localCompleteness hAffine hlocal
    (AffinePinnedModel.openPinnedLabelCompleteness hAffine)

end Langlands.GroupScheme
