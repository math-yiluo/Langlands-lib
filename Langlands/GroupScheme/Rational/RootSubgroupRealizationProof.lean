import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootSubgroupWeightExclusion
import Langlands.GroupScheme.Rational.TorusUnipotenceProof
import Langlands.GroupScheme.Rational.TorusSplitUnipotenceProof

/-! # Direct assembly of actual relative-root realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

private theorem cyclicSpan_eq_positive
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) =
      positiveWeightSpan i a := by
  rw [semigroupWeightSpan, positiveWeightSpan]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    obtain ⟨n, _, hn, he⟩ := χ.property
    rw [← he, actionWeightSpace_conjugation]
    exact le_iSup_of_le ⟨n, hn⟩ le_rfl
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le
      ⟨n.val • a, n.val, n.property, n.property, rfl⟩
      (by rw [actionWeightSpace_conjugation])

/-- Actual relative-root functors have smooth connected closed split-unipotent
representatives, stable under the torus, with the full positive Lie image. -/
theorem rootSubgroupRealization : RootSubgroupRealizationStatement.{u} := by
  intro k _ G hG S i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro a ha
  have ha0 : a ≠ 0 := (mem_relativeRoots.mp ha).1
  have hS : IsSplitTorus S.toGrp := hi.1.1
  obtain ⟨U, j, hj, hclosed, hsmooth, hconn⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha0
  let : IsAffineHom U.X.hom := hclosed.isAffineHom
  have hLie : HasLieImage (subgroup i a) (positiveWeightSpan i a) := by
    rw [← cyclicSpan_eq_positive]
    exact hasLieImage_subgroup i a hS ha0
  let b := subgroupAction i a j hj
  have hzero : actionWeightSpace b 0 = ⊥ :=
    subgroupAction_zero_weightSpace_eq_bot_of_hasLieImage i a hS j hj hLie ha0
  have hu : IsUnipotent U :=
    torusActionUnipotence k U hsmooth inferInstance hconn S hS b hzero
  have hs : IsSplitUnipotent U :=
    torusActionSplitUnipotence k U hsmooth inferInstance hconn hu S hS b hzero
  exact ⟨U, j, hj, hclosed, hsmooth, hconn, hu, hs, subgroup_isStable i a, hLie⟩

end Langlands.GroupScheme.RelativeRoot
