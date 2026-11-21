import Langlands.GroupScheme.HomogeneousCharacterProducts
import Langlands.GroupScheme.MatrixRepresentation.SemisimpleCoordinates
import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.Reductive.SplitBorelCell

/-! # The simple socle and weight bounds of induction from the opposite Borel -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open HomogeneousQuotientFromEmbedding

/-- The entire representation induced from the opposite Borel has a unique simple
subrepresentation of highest weight `λ` when `λ` is dominant. Each occurring weight lies
between the longest Weyl translate of `λ` and `λ` in the simple-root order. -/
def SplitBorelInducedSocleAndWeightsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (D : HomogeneousQuotient p.negativeBorelHom) [IsProper D.scheme.hom]
    (lam : characterLattice p.torus),
    letI : Mono p.negativeBorelHom.hom.hom := p.isRepresentedBy_negativeBorelHom.1
    let ρ := inducedRepresentation p.negativeBorelHom D (p.borelCharacter lam)
    (p.IsDominantWeight lam →
      ∃ W : Submodule k (Fin (Module.finrank k (inducedSpace p.negativeBorelHom
          (p.borelCharacter lam))) → k),
        ρ.IsSimpleStableSubspace W ∧
        (∀ W', ρ.IsSimpleStableSubspace W' → W' = W) ∧
        ∃ C : MatrixRepresentation.StableSubspaceRepresentation ρ W,
          p.IsHighestWeight C.representation lam) ∧
    ∀ μ : characterLattice p.torus, p.representationWeightSpace ρ μ ≠ ⊥ →
      lam - μ ∈ p.positiveRootMonoid ∧
      ∀ w : p.rootDatum.weylGroup,
        (∀ i : p.rootIndex, p.base.IsPos (w.val.indexEquiv i) ↔ ¬ p.base.IsPos i) →
        μ - w.val • lam ∈ p.positiveRootMonoid

end Langlands.GroupScheme
