import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Lie.RepresentationSubquotient

/-! # Highest-weight representations of a split reductive group under extension of the base field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Highest-weight representations of a split reductive group under extension of the base
field (Milne, *Algebraic Groups* (2017), 22.4 and 22.5). For a supplied split pinning `p` of
`G` over a field `k`:

* every matrix intertwining a highest-weight representation with itself is a scalar matrix;
* a highest-weight representation stays simple after extension to any field `K ⊇ k`;
* after extension to an algebraic field `K ⊇ k`, a representation of highest weight `lam`
  has highest weight the base change of `lam` for the base change of `p`;
* every semisimple representation of `G_K` over any field `K ⊇ k` is isomorphic to the base
  change of a semisimple representation of `G` over `k`. -/
def SplitHighestWeightBaseChangeStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G),
    let IsSemisimpleRep : {F : Type u} → [Field F] →
        {H : GroupScheme (Spec (CommRingCat.of F))} → {m : ℕ} →
        MatrixRepresentation H (Fin m) → Prop :=
      fun {F} _ {_} {m} σ => sSup {W : Submodule F (Fin m → F) | σ.IsStableSubspace W ∧
        W ≠ ⊥ ∧ ∀ U : Submodule F (Fin m → F), σ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤
    (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus),
      p.IsHighestWeight ρ lam →
        ∀ C : Matrix (Fin n) (Fin n) k, ρ.Intertwines ρ C → ∃ c : k, C = Matrix.scalar (Fin n) c) ∧
    (∀ (K : Type u) [Field K] [Algebra k K]
      (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus),
      p.IsHighestWeight ρ lam → (ρ.baseChange (algebraBaseMap k K)).IsIrreducible) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K],
      haveI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus),
        p.IsHighestWeight ρ lam →
          (p.baseChange (F := K)).IsHighestWeight (ρ.baseChange (algebraBaseMap k K))
            (characterLattice.baseChange (algebraBaseMap k K) p.torus lam)) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] (m : ℕ)
      (ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin m)),
      IsSemisimpleRep ρ' →
        ∃ ρ : MatrixRepresentation G (Fin m), IsSemisimpleRep ρ ∧
          ∃ C : Matrix (Fin m) (Fin m) K,
            (ρ.baseChange (algebraBaseMap k K)).Intertwines ρ' C ∧
              Function.Bijective C.mulVecLin)

end Langlands.GroupScheme
