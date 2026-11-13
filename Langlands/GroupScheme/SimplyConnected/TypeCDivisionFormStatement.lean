import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Division-algebra presentations and indices of simply connected type-C groups

The general classification statement below is a prerequisite. It is not proved
in this module. It constructs its algebra and form from the actual group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- General type-C classification by trace-valued antihermitian division forms,
including the actual distinguished vertices and an isomorphism of group schemes.
The assertion is over all fields, including characteristic two, and is unproved. -/
def TypeCDivisionFormStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (e : d.Vertex ≃ Fin n),
    2 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) →
      ∃ (degree m : ℕ) (_ : NeZero m)
        (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
        0 < degree ∧ m * degree = 2 * n ∧
        Module.finrank K D = degree ^ 2 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
              ∃ H : Matrix (Fin m) (Fin m) D,
                σ.IsAntihermitian H ∧ IsUnit H ∧
                (σ.wittIndex H : ℕ∞) = splitRank G ∧
                Nonempty (G ≅ σ.symplecticGroup H) ∧
                ∀ a : d.Vertex, a ∈ d.distinguishedVertices ↔
                  ∃ j : ℕ, 1 ≤ j ∧ (j : ℕ∞) ≤ splitRank G ∧
                    (e a).val + 1 = j * degree

end Langlands.GroupScheme
