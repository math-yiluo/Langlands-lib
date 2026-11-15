import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.Lie.RepresentationSubquotient

/-! # Classification of simple representations of a split reductive group by highest weight -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The fundamental theorem of highest weight for a supplied split pinning over an
arbitrary field: every dominant character is a highest weight; two highest-weight
representations are isomorphic exactly when their highest weights agree; and every
irreducible representation has a unique dominant highest weight. -/
def SplitHighestWeightClassificationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G),
    (∀ lam : characterLattice p.torus, p.IsDominantWeight lam →
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), p.IsHighestWeight ρ lam) ∧
    (∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m))
      (lam mu : characterLattice p.torus),
      p.IsHighestWeight ρ lam → p.IsHighestWeight σ mu →
        ((∃ C : Matrix (Fin m) (Fin n) k,
            ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin) ↔ lam = mu)) ∧
    (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible →
      ∃! lam : characterLattice p.torus, p.IsDominantWeight lam ∧ p.IsHighestWeight ρ lam)

end Langlands.GroupScheme
