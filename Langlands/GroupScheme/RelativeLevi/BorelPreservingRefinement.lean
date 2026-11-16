import Langlands.AlgebraicGeometry.AffineFppfRefinement
import Langlands.GroupScheme.LocalGroupIsoBorelRefinement

/-! # Affine fppf Borel-preserving refinements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H A B B' : GroupScheme S} {U : Over S}

/-- A single affine fppf cover on which a source conjugation makes the
local family preserve the specified subgroup ranges. -/
structure BorelPreservingFppfRefinement (e : LocalGroupIso G H U)
    (i : B ⟶ G) (j : B' ⟶ H) where
  cover : Over S
  map : cover ⟶ U
  cochain : cover ⟶ G.X
  isAffine : IsAffine cover.left
  flat : Flat cover.hom
  surjective : Surjective cover.hom
  locallyOfFinitePresentation : LocallyOfFinitePresentation cover.hom
  preserves : ((e.refine map).twist
    (AutomorphicAction.conjugation (𝟙 G)) cochain).PreservesSubgroup
      (SubgroupFunctor.range i) (SubgroupFunctor.range j)

/-- On a quasi-compact base, a single fppf local-isomorphism cover has an
affine fppf refinement with a Borel-preserving corrected local family. -/
def borelPreservingFppfRefinement [CompactSpace S]
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (e : LocalGroupIso G H U) (hG : IsReductive G) (hH : IsReductive H)
    (i : B ⟶ G) (j : B' ⟶ H)
    (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j) :
    BorelPreservingFppfRefinement e i j := by
  let d := e.borelPreservingRefinement hG hH i j hi hj
  let : Etale d.map.left := d.etale
  let : Surjective d.map.left := d.surjective
  let : Flat d.parameter.hom := by
    rw [← Over.w d.map]
    infer_instance
  let : Surjective d.parameter.hom := by
    rw [← Over.w d.map]
    infer_instance
  let : LocallyOfFinitePresentation d.parameter.hom := by
    rw [← Over.w d.map]
    infer_instance
  let R := Langlands.AlgebraicGeometry.affineFppfRefinement d.parameter
  refine {
    cover := R.cover
    map := R.map ≫ d.map
    cochain := R.map ≫ d.cochain
    isAffine := R.isAffine
    flat := R.flat
    surjective := R.surjective
    locallyOfFinitePresentation := R.locallyOfFinitePresentation
    preserves := ?_ }
  intro T b g
  have h := d.preserves (b ≫ R.map) g
  change e.toFun ((b ≫ R.map) ≫ d.map)
      ((AutomorphicAction.conjugation (𝟙 G)).act ((b ≫ R.map) ≫ d.cochain) g) ∈
        (SubgroupFunctor.range j).carrier T ↔
      g ∈ (SubgroupFunctor.range i).carrier T at h
  change e.toFun (b ≫ (R.map ≫ d.map))
      ((AutomorphicAction.conjugation (𝟙 G)).act (b ≫ (R.map ≫ d.cochain)) g) ∈
        (SubgroupFunctor.range j).carrier T ↔
      g ∈ (SubgroupFunctor.range i).carrier T
  simpa only [Category.assoc] using h

/-- A compatible quotient-action twist preserves the same subgroup ranges. -/
theorem BorelPreservingFppfRefinement.preservesSubgroup
    {e : LocalGroupIso G H U} {i : B ⟶ G} {j : B' ⟶ H}
    (d : BorelPreservingFppfRefinement e i j)
    (c : AutomorphicAction A G) (q : G ⟶ A)
    (hc : c.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    ((e.refine d.map).twist c (d.cochain ≫ q.hom.hom)).PreservesSubgroup
      (SubgroupFunctor.range i) (SubgroupFunctor.range j) := by
  rw [← twist_conjugation_eq _ c q hc]
  exact d.preserves

/-- The refined quotient-action twist retains all-refinement innerness. -/
theorem BorelPreservingFppfRefinement.hasInnerDiscrepancy
    {e : LocalGroupIso G H U} {i : B ⟶ G} {j : B' ⟶ H}
    (d : BorelPreservingFppfRefinement e i j)
    (c : AutomorphicAction A G) (q : G ⟶ A)
    (he : e.HasInnerDiscrepancy c) :
    ((e.refine d.map).twist c (d.cochain ≫ q.hom.hom)).HasInnerDiscrepancy c :=
  HasInnerDiscrepancy.twist (HasInnerDiscrepancy.refine he d.map) _

end Langlands.GroupScheme.LocalGroupIso
