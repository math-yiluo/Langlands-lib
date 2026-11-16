import Langlands.GroupScheme.Reductive.AffinePinnedAtlasEffectivity
import Langlands.GroupScheme.Reductive.AffinePinnedAtlasSolutionInner
import Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormStatement

/-! # Quasi-split inner forms from a natural pinned comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- An actual quasi-split group, Borel and maximal torus, with an inner local
identification with the original group on a surjective étale cover. -/
structure RelativeQuasiSplitInnerFormData {S : Scheme.{u}}
    (G : GroupScheme S) {Q : GroupScheme S} (c : AutomorphicAction Q G) where
  group : GroupScheme S
  cover : Over S
  etale : Etale cover.hom
  surjective : Surjective cover.hom
  localIso : LocalGroupIso G group cover
  inner : localIso.HasInnerDiscrepancy c
  geometry : RelativeQuasiSplitTorusData group

/-- Construct the actual quasi-split inner form of any reductive group,
conditional only on a supplied natural pinned comparison. -/
def relativeQuasiSplitInnerFormOfPinnedComparison
    (P : RelativePinnedComparison.{u}) {S : Scheme.{u}} {G Q : GroupScheme S}
    (hG : IsReductive G) (p : G ⟶ Q)
    (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction Q G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G)) :
    RelativeQuasiSplitInnerFormData G c := by
  let A := AffinePinnedAtlas.ofReductive hG
  let s := A.solution P hG
  exact
    { group := s.obj
      cover := Over.mk A.projection
      etale := inferInstanceAs (Etale A.projection)
      surjective := inferInstanceAs (Surjective A.projection)
      localIso := A.solutionLocalIso P s
      inner := A.solutionLocalIso_hasInnerDiscrepancy P s p hp c hc
      geometry := A.quasiSplitTorusData P hG }

/-- Natural pinned comparison existence implies the unchanged arbitrary-base
quasi-split inner-form existence statement. -/
theorem relativeQuasiSplitInnerFormExistence_of_pinnedComparison
    (hP : RelativePinnedComparisonExistenceStatement.{u}) :
    RelativeQuasiSplitInnerFormExistenceStatement.{u} := by
  obtain ⟨P⟩ := hP
  intro S G hG Q p hp c hc
  let d := relativeQuasiSplitInnerFormOfPinnedComparison P hG p hp c hc
  refine ⟨d.group, ⟨d.cover, d.etale, d.surjective, d.localIso, d.inner⟩,
    d.geometry.quasiSplit, d.geometry.borel.obj, d.geometry.borel.inclusion,
    d.geometry.torus, d.geometry.torusInclusion, d.geometry.borel.isBorel,
    d.geometry.torusIsTorus, d.geometry.torusClosed, d.geometry.torusMaximal,
    d.geometry.torus_le_borel⟩

end Langlands.GroupScheme
