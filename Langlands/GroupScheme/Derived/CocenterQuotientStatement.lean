import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.GaloisPointRational

/-! # The cocenter quotient of a connected reductive group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The cocenter `M / M_der` of a connected reductive group `M` over a field `k` exists as an
affine commutative group scheme `D'` that is a torus, with `q : M → D'` an fppf quotient by the
derived subgroup. Every maximal torus `t : T → M` maps onto `D'` on cocharacters: over every field
`E/k` splitting `T`, the base change of `D'` is split and `ν ↦ ν ≫ (t ≫ q)_E` is surjective.
Derived formulation of KP §2.6(a) and the proof of KP Lemma 2.6.27; not a numbered KP result. -/
def CocenterQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (M D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M),
    IsConnectedReductive M → IsDerivedSubgroup d →
    ∃ (D' : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ D'.toGrp),
      IsAffine D'.X.left ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q ∧
      IsTorus D'.toGrp ∧
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ M),
        IsMaximalTorus t →
        ∀ (E : Type u) [Field E] [Algebra k E],
          IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp) →
          IsSplitTorus (GaloisPointComparison.baseChanged k E D'.toGrp) ∧
          Function.Surjective
            (fun ν : cocharacterLattice
                ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)).obj T) =>
              ν ≫ (CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map
                (Additive.ofMul (t ≫ q) : T ⟶ D'))

end Langlands.GroupScheme
