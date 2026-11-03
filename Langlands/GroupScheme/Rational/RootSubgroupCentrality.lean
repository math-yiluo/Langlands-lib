import Langlands.GroupScheme.Rational.WeightSupportCongruence
import Langlands.GroupScheme.Rational.WeightSupportVanishing

/-! # Centrality of the doubled relative-root subgroup from cyclic tails -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section CentralDouble

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}

/-- The doubled-character subgroup is contained in and centralizes the original
character subgroup, on every scheme test. -/
def HasCentralDoubleSubgroup (i : S.toGrp ⟶ G) (a : characterLattice S) : Prop :=
  subgroup i (2 • a) ≤ subgroup i a ∧
    ∀ (T : Over B) (x y : T ⟶ G.X),
      x ∈ (subgroup i (2 • a)).carrier T →
      y ∈ (subgroup i a).carrier T → Commute x y

end CentralDouble

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The cyclic comparison identifies the doubled subgroup with a subgroup
of the original one, without a reduced-root restriction. -/
theorem double_subgroup_le_of_cyclicComparison
    (hcyclic : CyclicRootFunctorComparisonStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) :
    subgroup i (2 • a) ≤ subgroup i a := by
  let b := AutomorphicAction.conjugation i
  have hfirst := hcyclic k G hG inferInstance S hS i a ha
  have hdouble := hcyclic k G hG inferInstance S hS i (2 • a)
    (hS.nsmul_ne_zero ha (by omega))
  calc
    subgroup i (2 • a) = weightFiltration b (2 • a) 1 := hdouble.symm
    _ ≤ weightFiltration b a 2 :=
      semigroupSubgroup_mono b (cyclicTail_double_le a)
    _ ≤ weightFiltration b a 1 := weightFiltration_antitone b a (by omega)
    _ = subgroup i a := hfirst

/-- Once no higher positive multiple is a root, the third commutator tail is
trivial and the doubled relative-root subgroup centralizes the first. -/
theorem double_subgroup_commute_of_noHigherRoots
    (hreal : SemigroupRealizationStatement.{u})
    (hcomm : SemigroupCommutatorStatement.{u})
    (hcyclic : CyclicRootFunctorComparisonStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X)
    (hx : x ∈ (subgroup i (2 • a)).carrier T)
    (hy : y ∈ (subgroup i a).carrier T) : Commute x y := by
  let b := AutomorphicAction.conjugation i
  have hweights : ∀ n : ℕ, 3 ≤ n → n • a ∉ actionWeightSupport b ⊤ := by
    intro n hn hsupport
    exact hhigh n hn
      ((mem_actionWeightSupport_conjugation_iff i
        (hS.nsmul_ne_zero ha (by omega))).mp hsupport)
  have htwo := weightFiltration_two_eq_double b a hweights
  have hthree : weightFiltration b a 3 = ⊥ :=
    weightFiltration_eq_bot_of_noRelativeRoots hreal hG hS i ha 3
      (fun n hn _ => hhigh n hn)
  have hx' : x ∈ (weightFiltration b a 2).carrier T := by
    rw [htwo, hcyclic k G hG inferInstance S hS i (2 • a)
      (hS.nsmul_ne_zero ha (by omega))]
    exact hx
  have hy' : y ∈ (weightFiltration b a 1).carrier T := by
    rw [hcyclic k G hG inferInstance S hS i a ha]
    exact hy
  exact commute_of_weightFiltration_eq_bot hcomm hG hS b a 2 1 hthree T x y hx' hy'

/-- The exact centrality part of the two-step root-group target follows
from the three source statements and the higher-root exclusion. -/
theorem hasCentralDoubleSubgroup_of_noHigherRoots
    (hreal : SemigroupRealizationStatement.{u})
    (hcomm : SemigroupCommutatorStatement.{u})
    (hcyclic : CyclicRootFunctorComparisonStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    HasCentralDoubleSubgroup i a :=
  ⟨double_subgroup_le_of_cyclicComparison hcyclic hG hS i ha,
    double_subgroup_commute_of_noHigherRoots hreal hcomm hcyclic hG hS i ha hhigh⟩

end Langlands.GroupScheme.RelativeRoot
