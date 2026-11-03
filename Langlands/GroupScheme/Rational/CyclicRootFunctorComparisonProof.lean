import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupStabilityProof
import Langlands.GroupScheme.Rational.CyclicWeightContraction
import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # The first cyclic-tail functor is the intrinsic relative root functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction.Affine

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (b : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

/-- The identity-limit representative of every affine multiplicative-group
action over a field is connected. -/
theorem connectedSpace_unipotentScheme :
    ConnectedSpace (unipotentScheme b).X.left := by
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
    isSplitTorus_gm.isAffineHom
  let : IsAffine b.semidirectProduct.X.left :=
    isAffine_of_isAffineHom b.semidirectProduct.X.hom
  exact DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent
    b.semidirectProduct b.semidirectInr
    (Dynamic.Affine.isRepresentedBy_unipotentHom b.semidirectInr)

/-- Connectedness holds for every all-test representative of the action's
identity-limit functor, with no smoothness premise. -/
theorem connectedSpace_of_isRepresentedBy_unipotent
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : b.unipotent.IsRepresentedBy j) : ConnectedSpace U.X.left := by
  let : ConnectedSpace (unipotentScheme b).X.left :=
    connectedSpace_unipotentScheme b
  exact DynamicConnected.connectedSpace_of_iso
    (hj.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom b))

end AutomorphicAction.Affine

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [hAff : IsAffineHom G.X.hom] [hG : Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)

include hAff hG hS ha

/-- The intrinsic root functor has a smooth connected closed representative
for every nonzero character, without ambient connectedness. -/
theorem subgroup_isSmoothConnectedClosed_of_ne_zero :
    IsSmoothConnectedClosed (subgroup i a) := by
  obtain ⟨C, j, hj, hjc, hCs, _⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance S hS i a ha
  let : IsAffineHom C.X.hom := by
    let : IsClosedImmersion j.hom.hom.left := hjc
    rw [← j.hom.hom.w]
    infer_instance
  let : Smooth C.X.hom := hCs
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k S hS a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  let b := quotientAction i a j hj
  refine ⟨AutomorphicAction.Affine.unipotentScheme b,
    AutomorphicAction.Affine.unipotentHom b ≫ j, ?_,
    (AutomorphicAction.Affine.isClosedSubgroup_unipotentHom b).comp hjc,
    AutomorphicAction.Affine.smooth_unipotentScheme b,
    AutomorphicAction.Affine.connectedSpace_unipotentScheme b⟩
  rw [quotientActionComparison _ _ _ _ i a j hj hjc]
  exact (AutomorphicAction.Affine.isRepresentedBy_unipotentHom b).comp hj

/-- Equality of the generated first cyclic tail and the actual character-orbit
subgroup on every test scheme. -/
theorem weightFiltration_one_eq_subgroup :
    weightFiltration (AutomorphicAction.conjugation i) a 1 = subgroup i a := by
  apply le_antisymm (weightFiltration_one_le_subgroup hS i a ha)
  exact generator_le_semigroupSubgroup (AutomorphicAction.conjugation i)
    (cyclicTail a 1) (subgroup i a)
    ⟨subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha, subgroup_isStable i a,
      actionWeightSupport_subset_of_tangentSubmodule_le
        (AutomorphicAction.conjugation i) hS (cyclicTail a 1) (subgroup i a)
        (le_of_eq (tangentSubmodule_subgroup i a hS ha))⟩

end RelativeRoot

namespace RelativeRoot

/-- The exact published cyclic-root comparison proposition at arbitrary universe. -/
theorem cyclicRootFunctorComparison : CyclicRootFunctorComparisonStatement.{u} := by
  intro k _ G hG hAff S hS i a ha
  let : Smooth G.X.hom := hG
  let : IsAffineHom G.X.hom := hAff
  exact weightFiltration_one_eq_subgroup hS i a ha

end RelativeRoot

end Langlands.GroupScheme
