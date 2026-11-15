import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Characters of representations of a split reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The character theorem for a supplied split pinning over an arbitrary field
(Milne, *Algebraic Groups* (2017), Theorem 22.38). The character of a representation `ρ`
is its weight-multiplicity function `lam ↦ dim ρ_lam` for the split maximal torus. First,
this function has finite support and is invariant under the reflections of the root datum
(so it lies in `ℤ[X]^W`). Second, two semisimple representations with the same character
are isomorphic (injectivity of the character map on the Grothendieck group). Third, every
finitely supported reflection-invariant integer function on the character lattice is the
difference of the characters of two representations (the image is all of `ℤ[X]^W`). -/
def SplitRepresentationCharacterStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G),
    let IsSemisimpleRep : {n : ℕ} → MatrixRepresentation G (Fin n) → Prop :=
      fun {n} σ => sSup {W : Submodule k (Fin n → k) | σ.IsStableSubspace W ∧
        W ≠ ⊥ ∧ ∀ U : Submodule k (Fin n → k), σ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤
    (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      (Function.support fun lam : characterLattice p.torus =>
        Module.finrank k (p.representationWeightSpace ρ lam)).Finite ∧
      ∀ (i : p.rootIndex) (lam : characterLattice p.torus),
        Module.finrank k (p.representationWeightSpace ρ (p.rootDatum.reflection i lam)) =
          Module.finrank k (p.representationWeightSpace ρ lam)) ∧
    (∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
      IsSemisimpleRep ρ → IsSemisimpleRep σ →
      (∀ lam : characterLattice p.torus,
        Module.finrank k (p.representationWeightSpace ρ lam) =
          Module.finrank k (p.representationWeightSpace σ lam)) →
      ∃ C : Matrix (Fin m) (Fin n) k, ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin) ∧
    ∀ f : characterLattice p.torus →₀ ℤ,
      (∀ (i : p.rootIndex) (lam : characterLattice p.torus),
        f (p.rootDatum.reflection i lam) = f lam) →
      ∃ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
        ∀ lam : characterLattice p.torus,
          f lam = (Module.finrank k (p.representationWeightSpace ρ lam) : ℤ) -
            Module.finrank k (p.representationWeightSpace σ lam)

end Langlands.GroupScheme
