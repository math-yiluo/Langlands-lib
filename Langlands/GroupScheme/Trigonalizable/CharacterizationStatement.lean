import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.GroupTheory.Finiteness

/-! # Characterizations of trigonalizable groups (Milne 16.2) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.2: for an affine algebraic group `G` over a field `k`, being
trigonalizable is equivalent to each of the following:
(b) every finite-dimensional matrix representation stabilizes a maximal flag;
(c) `G` admits a closed embedding into the upper triangular group `T_N` for some `N`;
(d) `G` has a normal unipotent closed subgroup `U` with a fppf quotient `G ⟶ D(Λ)` by `U` onto
a diagonalizable group, `Λ` finitely generated. -/
def TrigonalizableCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    (IsTrigonalizable G ↔
      ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
        ∃ W : Fin (Fintype.card n + 1) → Submodule k (n → k),
          Monotone W ∧ (∀ i, Module.finrank k (W i) = i.val) ∧
            ∀ i, ρ.IsStableSubspace (W i)) ∧
    (IsTrigonalizable G ↔
      ∃ (N : ℕ) (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
          (fun i => -(i.val : ℤ))),
        IsClosedSubgroup j) ∧
    (IsTrigonalizable G ↔
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
        (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
        (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
        IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)

end Langlands.GroupScheme
