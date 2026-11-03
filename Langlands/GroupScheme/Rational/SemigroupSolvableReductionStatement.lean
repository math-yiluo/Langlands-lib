import Langlands.GroupScheme.Rational.RootProductStatement

/-! # The algebraically closed unipotent core and solvable reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact ordered-product assertion for smooth connected affine unipotent
groups over algebraically closed fields, with the original cross-exclusion. -/
def UnipotentSemigroupOrderedProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (_hConn : ConnectedSpace G.X.left) (_hUnip : IsUnipotent G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    ∀ (n : ℕ) (Ψ : Fin n → Set (characterLattice S)),
      (⋃ r, Ψ r) = actionWeightSupport b ⊤ →
      (∀ r q : Fin n, r ≠ q → Disjoint (Ψ r) (Ψ q)) →
      (∀ r q : Fin n, r ≠ q →
        Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ q) : Set (characterLattice S))) →
      ∃ (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G),
        (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
          IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
        IsIso (orderedMultiplication j)

/-- The first reduction in CGP 3.3.11: proving the algebraically closed
unipotent core suffices for the exact published target over every field.
The reduction includes scalar extension and descent. -/
def SemigroupSolvableReductionStatement : Prop :=
  UnipotentSemigroupOrderedProductStatement.{u} → SemigroupOrderedProductStatement.{u}

end Langlands.GroupScheme.RelativeRoot
