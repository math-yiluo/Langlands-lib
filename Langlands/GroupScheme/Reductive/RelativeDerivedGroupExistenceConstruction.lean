import Langlands.GroupScheme.Reductive.LocalCorootQuotient
import Langlands.GroupScheme.Reductive.CorootQuotientLocalAssembly

/-! # Constructed coroot quotients on every affine pinned model -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The local construction discharges the exact local coefficient-ring input. -/
theorem relativeDerivedLocalCorootQuotientExistence :
    RelativeDerivedLocalCorootQuotientExistenceStatement.{u} := by
  intro M _ _
  let q := RelativeDerived.localCorootQuotient M.reductive M.inclusion M.closed
    M.maximal M.fibrewiseRootDatum
  exact ⟨q.val, q.property.1⟩

namespace RelativeDerived

/-- The actual smooth surjective coroot quotient on any supplied affine
  pinned model, with the prescribed torus restriction and full geometric
  semisimple kernel. No locality condition is imposed on its ring. -/
def pinnedCorootQuotient (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates] :
    {q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp //
      M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum ∧
      Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      ∀ s : M.base, IsSemisimple
        (kernel ((GroupScheme.baseChange (geometricPoint M.base s)).map q))} := by
  let h := exists_smooth_corootQuotient_of_local
    relativeDerivedLocalCorootQuotientExistence M
  let q := h.choose
  have hq := h.choose_spec.1
  exact ⟨q, hq, h.choose_spec.2.1, h.choose_spec.2.2,
    isSemisimple_corootQuotient_geometricKernel M q hq⟩

end RelativeDerived

/-- The split affine torus-quotient existence input is fully constructed. -/
theorem relativeDerivedSplitTorusQuotientExistence :
    RelativeDerivedSplitTorusQuotientExistenceStatement.{u} :=
  relativeDerivedSplitTorusQuotient_of_localCorootQuotient
    relativeDerivedLocalCorootQuotientExistence

/-- The remaining global descent input is relative semisimple fppf perfectness. -/
theorem relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u}) :
    RelativeDerivedGroupExistenceStatement.{u} :=
  relativeDerivedGroupExistence_of_localCorootQuotient hperf
    relativeDerivedLocalCorootQuotientExistence

end Langlands.GroupScheme
