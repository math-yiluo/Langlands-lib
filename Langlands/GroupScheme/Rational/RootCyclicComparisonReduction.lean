import Langlands.GroupScheme.Rational.CocharacterWeightSums

/-! # Cyclic comparison for actual relative roots from root uniqueness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

private theorem cyclicWeightSpan_eq_positiveWeightSpan
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) =
      positiveWeightSpan i a := by
  rw [semigroupWeightSpan_conjugation, adjointSemigroupWeightSpan, positiveWeightSpan]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    obtain ⟨n, _, hn, he⟩ := χ.property
    rw [← he]
    exact le_iSup_of_le ⟨n, hn⟩ le_rfl
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le
      ⟨n.val • a, n.val, n.property, n.property, rfl⟩ le_rfl

/-- The first positive cyclic term agrees with the actual root functor for
relative roots of a connected reductive group and a maximal split torus. -/
def ActualRootCyclicComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
    letI := hG.isAffineHom
    ∀ a : characterLattice S, a ∈ relativeRoots i →
      weightFiltration (AutomorphicAction.conjugation i) a 1 = subgroup i a

/-- Realization of the cyclic semigroup and the actual-root uniqueness
property imply the comparison on actual relative roots. -/
theorem actualRootCyclicComparison_of_realization_uniqueness
    (hRealization : SemigroupRealizationStatement.{u})
    (hUniqueness : RootSubgroupUniquenessStatement.{u}) :
    ActualRootCyclicComparisonStatement.{u} := by
  intro k _ G hG S i hi
  let := hG.isAffineHom
  intro a ha
  have hData :=
    hRealization k G hG.smooth hG.isAffineHom S hi.1.1
      (AutomorphicAction.conjugation i) (cyclicTail a 1)
  obtain ⟨H, j, hRep, hClosed, hSmooth, hConn⟩ := hData.1
  have hStable : (AutomorphicAction.conjugation i).IsStable
      (SubgroupFunctor.range j) := by
    rw [hRep.2]
    exact hData.2.1
  have hLie : HasLieImage (SubgroupFunctor.range j) (positiveWeightSpan i a) := by
    rw [hRep.2, ← cyclicWeightSpan_eq_positiveWeightSpan]
    exact hData.2.2.1
  exact hRep.2.symm.trans
    (hUniqueness k G hG S i hi a ha H j hClosed hSmooth hConn hStable hLie)

end Langlands.GroupScheme.RelativeRoot
