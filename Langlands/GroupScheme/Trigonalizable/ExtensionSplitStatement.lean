import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.Finiteness

/-! # Splitting of trigonalizable groups (Milne 16.26) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.26: let `G` be an affine algebraic group over a field `k` with a
normal unipotent closed subgroup `i : U ⟶ G` and an fppf quotient `q : G ⟶ D(Λ)` by it onto a
diagonalizable group (so `G` is trigonalizable and `U = G_u`, Milne 16.2(d)). The extension
`e → U → G → D(Λ) → e` splits, i.e. `q` has a homomorphic section, in each of the cases
(a) `k` is algebraically closed; (b) `k` is perfect and `U` is smooth and connected;
(c) `k` is perfect and `D(Λ)` is connected. -/
def TrigonalizableExtensionSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
      (IsAlgClosed k ∨ (PerfectField k ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left) ∨
        (PerfectField k ∧
          ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X.left)) →
      ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _

end Langlands.GroupScheme
