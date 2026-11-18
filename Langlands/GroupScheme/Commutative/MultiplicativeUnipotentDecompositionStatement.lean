import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.Perfect

/-! # Multiplicative and unipotent parts of a commutative algebraic group (Milne 16.13) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.13: let `G` be a commutative affine algebraic group over a field `k`.
(a) `G` has a closed subgroup `s : S ⟶ G` of multiplicative type containing every closed
subgroup of multiplicative type. It is characteristic: for every `k`-algebra `R` and every
automorphism `α` of `G_R`, `α(S_R) = S_R`. The fppf quotient `q : G ⟶ Q` by it is unipotent.
(b) If `k` is perfect, then multiplication `U × S → G` is an isomorphism for some unipotent
closed subgroup `U` and some closed subgroup `S` of multiplicative type. For every such
decomposition, `U` contains every unipotent closed subgroup and `S` contains every closed
subgroup of multiplicative type. -/
def CommutativeMultiplicativeUnipotentDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    (∃ (S Q : GroupScheme (Spec (CommRingCat.of k))) (s : S ⟶ G) (q : G ⟶ Q),
      IsClosedSubgroup s ∧ IsMultiplicativeType S ∧
        (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → IsMultiplicativeType H →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range s) ∧
        (∀ (R : Type u) [CommRing R] [Algebra k R],
          let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          ∀ α : F.obj G ≅ F.obj G,
            SubgroupFunctor.range (F.map s ≫ α.hom) = SubgroupFunctor.range (F.map s)) ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q ∧ IsUnipotent Q) ∧
    (PerfectField k →
      (∃ (U S : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G) (s : S ⟶ G),
        IsClosedSubgroup u ∧ IsUnipotent U ∧ IsClosedSubgroup s ∧ IsMultiplicativeType S ∧
          IsIso (subgroupMultiplication u s)) ∧
      ∀ (U S : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G) (s : S ⟶ G),
        IsClosedSubgroup u → IsUnipotent U → IsClosedSubgroup s → IsMultiplicativeType S →
          IsIso (subgroupMultiplication u s) →
            (∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
              IsClosedSubgroup j → IsUnipotent V →
                SubgroupFunctor.range j ≤ SubgroupFunctor.range u) ∧
            ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
              IsClosedSubgroup h → IsMultiplicativeType H →
                SubgroupFunctor.range h ≤ SubgroupFunctor.range s)

end Langlands.GroupScheme
