import Langlands.GroupScheme.Rational.FundamentalRepresentations

/-! # Every character of a closed split torus occurs as a weight (Milne 22.13) -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, *Algebraic Groups* (2017), Proposition 22.13: every character of the split
maximal torus of a split reductive group occurs as a weight in some finite-dimensional
representation. The first conjunct states this for every closed split torus subgroup of an
arbitrary affine group scheme over a field; the second states it for split pinnings.
This is a statement only; nothing is proved here. -/
def SplitTorusCharacterWeightStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom],
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (hT : IsSplitTorus T.toGrp), IsClosedSubgroup i →
        letI := hT.isAffineHom
        ∀ χ : rationalCharacters T.toGrp,
          ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
            (ρ.restrict i).characterSpace χ ≠ ⊥) ∧
    ∀ (p : SplitPinning G) (lam : characterLattice p.torus),
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        p.representationWeightSpace ρ lam ≠ ⊥

end Langlands.GroupScheme
