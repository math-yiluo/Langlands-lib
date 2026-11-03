import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.WeightSemigroupSupport
import Langlands.GroupScheme.Rational.CocharacterWeightSums
import Langlands.GroupScheme.Rational.RelativeRootSignSupport
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # Actual-root detection of dynamic parabolic inclusion through Lie algebras -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For a split torus, inclusion between two semigroup weight spans is detected
by inclusion of the semigroups on actual ambient action weights. -/
theorem semigroupWeightSpan_le_iff_on_weightSupport
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A A' : AddSubsemigroup (characterLattice S)) :
    semigroupWeightSpan b A ≤ semigroupWeightSpan b A' ↔
      SemigroupWeightSupportLE b A A' := by
  constructor
  · intro h χ hχ hχA
    obtain ⟨X, hX0, hXχ, _⟩ := hχ
    by_contra hχA'
    have hXA : X ∈ semigroupWeightSpan b A :=
      (le_iSup (fun ψ : A => actionWeightSpace b ψ.val) ⟨χ, hχA⟩) hXχ
    exact hX0 ((Submodule.disjoint_def.mp
      (disjoint_actionWeightSpace_semigroupWeightSpan b hS A' χ hχA'))
        X hXχ (h hXA))
  · intro h
    refine iSup_le fun χ => ?_
    by_cases hχ : actionWeightSpace b χ.val = ⊥
    · rw [hχ]
      exact bot_le
    · exact le_iSup (fun ψ : A' => actionWeightSpace b ψ.val)
        ⟨χ.val, h χ.val ((mem_actionWeightSupport_top b).mpr hχ) χ.property⟩

/-- The exact tangent submodule of a dynamic parabolic is the nonnegative
torus weight span. -/
theorem tangentSubmodule_parabolic_eq_semigroupWeightSpan
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    tangentSubmodule (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) =
      semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν) := by
  rw [semigroupWeightSpan_conjugation_nonnegative hS i ν]
  ext X
  exact (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i) X.toMul).2.1

/-- Parabolic inclusion always implies containment of the nonnegative regions
on actual roots; neither smoothness nor connectedness is needed. -/
theorem nonnegative_rootSupport_of_parabolic_le
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S)
    (h : Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)) :
    ∀ χ ∈ relativeRoots i,
      0 ≤ latticePairing S χ zeta → 0 ≤ latticePairing S χ eta := by
  apply (nonnegative_rootSupport_iff i zeta eta).mpr
  apply (semigroupWeightSpan_le_iff_on_weightSupport
    (AutomorphicAction.conjugation i) hS _ _).mp
  rw [← tangentSubmodule_parabolic_eq_semigroupWeightSpan hS i zeta,
    ← tangentSubmodule_parabolic_eq_semigroupWeightSpan hS i eta]
  intro X hX
  exact h _ hX

/-- On a smooth connected affine group, dynamic connectedness is the only
remaining structural premise for the actual-root parabolic inclusion criterion. -/
theorem parabolic_le_iff_nonnegative_rootSupport
    (hCo : DynamicConnectedStatement.{u}) [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ relativeRoots i,
        0 ≤ latticePairing S χ zeta → 0 ≤ latticePairing S χ eta := by
  constructor
  · exact nonnegative_rootSupport_of_parabolic_le hS i zeta eta
  · intro h
    have hspan := (semigroupWeightSpan_le_iff_on_weightSupport
      (AutomorphicAction.conjugation i) hS _ _).mpr
        ((nonnegative_rootSupport_iff i zeta eta).mp h)
    rw [semigroupWeightSpan_conjugation_nonnegative hS i zeta,
      semigroupWeightSpan_conjugation_nonnegative hS i eta] at hspan
    refine parabolic_le_parabolic_of_lieKernel dynamicSmooth hCo lieSubgroupEquality _ _
      ((SubgroupFunctor.range_comp_le _ i).trans
        ((range_le_centralizer_groupHom_comp i zeta).trans
          (Dynamic.centralizer_le_parabolic _))) ?_
    intro X hX
    exact (dynamicLie k G (CommGroupScheme.groupHom eta ≫ i) X).2.1.mpr
      (hspan ((dynamicLie k G (CommGroupScheme.groupHom zeta ≫ i) X).2.1.mp hX))

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme

/-- Generalized parabolic half of the root-sign inclusion target, reduced only
to connectedness of dynamic subgroups. -/
def RootSignParabolicInclusionsFromConnectedness : Prop :=
  DynamicConnectedStatement.{u} →
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (_hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (zeta eta : cocharacterLattice S),
    Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ relativeRoots i,
        0 ≤ latticePairing S χ zeta → 0 ≤ latticePairing S χ eta

theorem rootSignParabolicInclusions_of_connectedness :
    RootSignParabolicInclusionsFromConnectedness.{u} := by
  intro hCo k _ G _ _ _ S hS i zeta eta
  exact RelativeRoot.parabolic_le_iff_nonnegative_rootSupport hCo hS i zeta eta

end Langlands.GroupScheme
