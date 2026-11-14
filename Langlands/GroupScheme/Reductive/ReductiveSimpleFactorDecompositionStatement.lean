import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Torus.Lattice

/-! # The simple factors of a connected reductive group over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Exercise 5.5.2 (the reductive case of the
decomposition theorem, Theorem 5.1.19). Let `G` be a connected reductive group over a
field `k`, let `z : Z ⟶ G` be its maximal central torus, let `d : D ⟶ G` be its derived
group, and let `a i : A i ⟶ D` (`i` in a finite type `I`) list the `k`-simple factors of
`D`, that is, the minimal nontrivial smooth connected closed normal subgroups of `D`,
without repetition. Then
1. the composites `a i ≫ d` are exactly the minimal smooth connected closed normal
   non-central subgroups of `G`;
2. there is a homomorphism `p : ∏ A i ⟶ G` restricting to `a i ≫ d` on each factor, and
   the multiplication map `Z × ∏ A i ⟶ G`, `(x, y) ↦ z(x) p(y)`, is a central isogeny;
3. every smooth connected closed normal semisimple subgroup of `D` is normal in `G`.
This module states the proposition and does not prove it. -/
def ReductiveSimpleFactorDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G) (hz : IsCentral z),
      -- `z` is the maximal central torus
      IsClosedSubgroup z → IsTorus Z →
      (∀ (Z' : GroupScheme (Spec (CommRingCat.of k))) (z' : Z' ⟶ G),
        IsClosedSubgroup z' → IsCentral z' → IsTorus Z' →
        SubgroupFunctor.range z' ≤ SubgroupFunctor.range z) →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G), IsDerivedSubgroup d →
    -- smooth connected closed normal subgroups of an ambient field group
    let IsNormalSubgroup : ∀ {H K : GroupScheme (Spec (CommRingCat.of k))},
        (K ⟶ H) → Prop := fun {_ K} n =>
      IsClosedSubgroup n ∧ Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
        (SubgroupFunctor.range n).IsNormal
    -- minimal nontrivial ones among them
    let IsMinimalNormalSubgroup : ∀ {H K : GroupScheme (Spec (CommRingCat.of k))},
        (K ⟶ H) → Prop := fun {H _} n =>
      IsNormalSubgroup n ∧ SubgroupFunctor.range n ≠ ⊥ ∧
        ∀ (K' : GroupScheme (Spec (CommRingCat.of k))) (n' : K' ⟶ H),
          IsNormalSubgroup n' → SubgroupFunctor.range n' ≠ ⊥ →
          SubgroupFunctor.range n' ≤ SubgroupFunctor.range n →
          SubgroupFunctor.range n' = SubgroupFunctor.range n
    -- minimal ones among the non-central smooth connected closed normal subgroups
    let IsMinimalNoncentralNormalSubgroup : ∀ {H K : GroupScheme (Spec (CommRingCat.of k))},
        (K ⟶ H) → Prop := fun {H _} n =>
      IsNormalSubgroup n ∧ ¬ IsCentral n ∧
        ∀ (K' : GroupScheme (Spec (CommRingCat.of k))) (n' : K' ⟶ H),
          IsNormalSubgroup n' → ¬ IsCentral n' →
          SubgroupFunctor.range n' ≤ SubgroupFunctor.range n →
          SubgroupFunctor.range n' = SubgroupFunctor.range n
    ∀ (I : Type u) [Finite I] (A : I → GroupScheme (Spec (CommRingCat.of k)))
      (a : ∀ i, A i ⟶ D),
      -- the `a i` are the `k`-simple factors of `D`, listed without repetition
      (∀ i, IsMinimalNormalSubgroup (a i)) →
      Function.Injective (fun i => SubgroupFunctor.range (a i)) →
      (∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ D),
        IsMinimalNormalSubgroup n → ∃ i, SubgroupFunctor.range n = SubgroupFunctor.range (a i)) →
      -- 1. they are the minimal non-central smooth connected closed normal subgroups of `G`
      (∀ i, IsMinimalNoncentralNormalSubgroup (a i ≫ d)) ∧
      (∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ G),
        IsMinimalNoncentralNormalSubgroup n →
          ∃ i, SubgroupFunctor.range n = SubgroupFunctor.range (a i ≫ d)) ∧
      -- 2. the multiplication map `Z × ∏ A i ⟶ G` is a central isogeny
      (∃ p : pi A ⟶ G, (∀ i, piFactorInclusionHom A i ≫ p = a i ≫ d) ∧
        IsCentralIsogeny (prodHom z p (hz.commute_values p))) ∧
      -- 3. smooth connected closed normal semisimple subgroups of `D` are normal in `G`
      ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ D),
        IsNormalSubgroup n → IsSemisimple K → (SubgroupFunctor.range (n ≫ d)).IsNormal

end Langlands.GroupScheme
