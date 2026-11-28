import Langlands.GroupScheme.Absolute.SplitRootSubgroupStatement
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.IsogenyRootRestriction
import Langlands.GroupScheme.Rational.SemigroupIntersection
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof

/-! # Proof of the split root subgroup statement

This module proves `SplitRootSubgroupStatement` (Milne, *Algebraic Groups* (2017),
Theorem 21.11(b)–(c)). A monic linked rank-one parametrization of a root of the
reduced root datum represents the intrinsic root subgroup, and the Lie containment
criterion passes through the smooth connected semigroup model of the intersection
of the root subgroup with a torus-stable smooth closed subgroup. -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- An all-test torus-stable smooth closed subgroup contains the split root
subgroup whenever its tangent contains the selected root line. -/
private theorem splitRootSubgroup_le_of_weightSpace_le
    {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [Smooth H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {α : characterLattice T} (ha : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots i α) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hstable : (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range j))
    (hweight : weightSpace i α ≤ RelativeRoot.tangentSubmodule (SubgroupFunctor.range j)) :
    RelativeRoot.subgroup i α ≤ SubgroupFunctor.range j := by
  let : IsAffineHom H.X.hom := hj.isAffineHom
  have : Mono j.hom.hom.left := hj.mono
  let b := AutomorphicAction.conjugation i
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let c := b.onRepresentedSubgroup j hjrep hstable
  let A := RelativeRoot.cyclicTail α 1
  have hzero : 0 ∉ A := by
    rintro ⟨n, _, hn, heq⟩
    exact hT.nsmul_ne_zero ha (Nat.ne_of_gt hn) heq
  have hroot : RelativeRoot.semigroupSubgroup b A = RelativeRoot.subgroup i α :=
    RelativeRoot.weightFiltration_one_eq_subgroup hT i α ha
  have hcomap : (RelativeRoot.subgroup i α).comap j = RelativeRoot.semigroupSubgroup c A := by
    rw [← hroot]
    exact RelativeRoot.semigroup_comap_eq_of_zero_not_mem b c j
      (fun _ s x => b.onRepresentedSubgroup_act_comp j hjrep hstable s x)
      RelativeRoot.semigroupRealization CoordinateWeights.coordinateSemigroupComparison.2
      hT hj A hzero
  have hintersection : RelativeRoot.IsSmoothConnectedClosed
      (SubgroupFunctor.range j ⊓ RelativeRoot.subgroup i α) := by
    rw [← SubgroupFunctor.map_comap, hcomap]
    exact RelativeRoot.IsSmoothConnectedClosed.map j hj
      (RelativeRoot.isSmoothConnectedClosed_semigroupSubgroup c hT A)
  have hgeometry : RelativeRoot.IsSmoothConnectedClosed (RelativeRoot.subgroup i α) := by
    rw [← hroot]
    exact RelativeRoot.isSmoothConnectedClosed_semigroupSubgroup b hT A
  have htangent := RelativeRoot.tangentSubmodule_eq_weightSpace_of_noHigherRoots hT i ha hhigh
  have hintersectionLie : RelativeRoot.HasLieImage
      (SubgroupFunctor.range j ⊓ RelativeRoot.subgroup i α) (weightSpace i α) := by
    apply (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mpr
    rw [RelativeRoot.tangentSubmodule_inf, htangent, inf_eq_right.mpr hweight]
  have hle : SubgroupFunctor.range j ⊓ RelativeRoot.subgroup i α ≤
      RelativeRoot.subgroup i α := fun _ _ hx => hx.2
  have heq := hintersection.eq_of_le_of_hasLieImage hgeometry hle hintersectionLie
    ((RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mpr htangent)
  rw [← heq]
  exact fun _ _ hx => hx.1

set_option backward.isDefEq.respectTransparency false in
/-- The one-coordinate additive parametrization and the Lie containment
criterion for an actual split root subgroup. -/
theorem splitRootSubgroup : SplitRootSubgroupStatement.{u} := by
  intro k _ G hG T hT i hi α hα
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨J, _, P, hP, hred⟩ := rootDatumExistence k G hG T hT i hi
  let : P.IsReduced := hred
  obtain ⟨r, rfl⟩ : α ∈ Set.range P.root := hP.2.1 ▸ hα
  have hhigh := RelativeRoot.hasNoHigherRoots_of_isRootDatumOf P hT i hP r
  have hline := splitRootLieLine k G hG T hT i hi _ hα
  constructor
  · obtain ⟨xp, _, hxpMono, _, hxp, _, _⟩ :=
      exists_monic_rootRankOneRelations hG hT i hi P hP r
    let : Mono xp.hom.hom := hxpMono
    let hvector : RelativeRoot.IsVectorGroupOfDimension
        (VectorGroup.groupScheme (CommRingCat.of k) 1) 1 :=
      ⟨_, VectorGroup.isNaturalVectorCoordinates⟩
    let := hvector.isAffineHom
    let := hvector.smooth
    let := hvector.connectedSpace
    exact ⟨xp, HomImage.isClosedSubgroup_of_mono xp,
      hxp.represents_root_of_lie_line hG hT hi hα hhigh hline,
      hxp, hxp.lie_range_eq_weightSpace hline⟩
  · intro H j hj hsmooth hstable
    let : Smooth H.X.hom := hsmooth
    constructor
    · intro hc
      rw [← RelativeRoot.tangentSubmodule_eq_weightSpace_of_noHigherRoots hT i hα.1 hhigh]
      exact RelativeRoot.tangentSubmodule_mono hc
    · exact splitRootSubgroup_le_of_weightSpace_le hT i hα.1 hhigh j hj hstable

end Langlands.GroupScheme
