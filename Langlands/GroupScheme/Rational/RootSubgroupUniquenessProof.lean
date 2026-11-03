import Langlands.GroupScheme.Rational.CyclicTailWeightSpan
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof

/-! # Uniqueness of actual relative-root subgroups from their Lie weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The first cyclic-tail span is the full positive integral adjoint-weight
span, including all multiples that occur in a nonreduced relative root system. -/
theorem semigroupWeightSpan_cyclicTail_one_conjugation
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) =
      positiveWeightSpan i a := by
  rw [semigroupWeightSpan_cyclicTail]
  simp_rw [actionWeightSpace_conjugation]
  unfold positiveWeightSpan
  apply le_antisymm
  · apply iSup_le
    intro n
    exact le_iSup (fun m : {n : ℕ // 0 < n} => weightSpace i (m.val • a))
      ⟨n.val, n.property.2⟩
  · apply iSup_le
    intro n
    exact le_iSup (fun m : {n : ℕ // 1 ≤ n ∧ 0 < n} => weightSpace i (m.val • a))
      ⟨n.val, n.property, n.property⟩

/-- Semigroup realization and the cyclic comparison imply the exact
relative-root uniqueness statement. -/
theorem rootSubgroupUniqueness_of_semigroup
    (hRealization : SemigroupRealizationStatement.{u})
    (hCyclic : CyclicRootFunctorComparisonStatement.{u}) :
    RootSubgroupUniquenessStatement.{u} := by
  intro k _ G hG S i hi
  let := hG.isAffineHom
  intro a ha H j hj hSmooth hConn hStable hLie
  have : Mono j.hom.hom.left := hj.mono
  have hClosed : IsSmoothConnectedClosed (SubgroupFunctor.range j) :=
    ⟨H, j, ⟨Over.mono_of_mono_left _, rfl⟩, hj, hSmooth, hConn⟩
  have hLie' : HasLieImage (SubgroupFunctor.range j)
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1)) := by
    rw [semigroupWeightSpan_cyclicTail_one_conjugation]
    exact hLie
  have hUnique :=
    (hRealization k G hG.smooth hG.isAffineHom S hi.1.1
      (AutomorphicAction.conjugation i) (cyclicTail a 1)).2.2.2.2.2
        (SubgroupFunctor.range j) hClosed hStable hLie'
  exact hUnique.trans
    (hCyclic k G hG.smooth hG.isAffineHom S hi.1.1 i a (mem_relativeRoots.mp ha).1)

/-- The exact published uniqueness statement for actual relative-root
subgroups, at every universe and over every field. -/
theorem rootSubgroupUniqueness : RootSubgroupUniquenessStatement.{u} :=
  rootSubgroupUniqueness_of_semigroup semigroupRealization cyclicRootFunctorComparison

end Langlands.GroupScheme.RelativeRoot
