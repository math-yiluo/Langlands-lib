import Langlands.GroupScheme.Trigonalizable.ExtensionSplitStatement
import Mathlib.Algebra.CharP.Defs

/-! # Splitting over a finite étale diagonalizable quotient (SGA 3 XVII 5.2.3 i) c)) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- SGA 3 XVII, Lemme 5.2.3 i) c), for a diagonalizable quotient and a smooth kernel: let `G`
be an affine algebraic group over a perfect field `k` with a normal unipotent closed subgroup
`i : U ⟶ G` and an fppf quotient `q : G ⟶ D(Λ)` by it, where `Λ` is finite of order prime to
the characteristic exponent `p` of `k` (so that `D(Λ)` is finite étale). If `U` is smooth and
connected, then `q` has a homomorphic section. -/
def EtaleDiagonalizableExtensionSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    PerfectField k → Finite Λ → Nat.Coprime (Nat.card Λ) p →
    IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
    (SubgroupFunctor.range i).IsNormal →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
      ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _

end Langlands.GroupScheme
