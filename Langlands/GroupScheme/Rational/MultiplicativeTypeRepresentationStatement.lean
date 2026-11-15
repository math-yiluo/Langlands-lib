import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Basic

/-! # Representations of a group of multiplicative type over a field (Milne 12.30) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Representations of a group of multiplicative type over a field (Milne, *Algebraic
Groups* (2017), Theorem 12.30). Let `G` be an affine group scheme of multiplicative type
over a field `k`, let `Ks` be a separable closure of `k`, and let `Γ = Aut_k(Ks)` act on
`X^*(G) = X(G_{Ks})` by `rationalCharacters.galoisRepresentation`. The weights of a
representation `ρ` of `G` on `kⁿ` are the characters `χ` of `G_{Ks}` whose eigenspace in
the scalar extension of `ρ` to `Ksⁿ` is nonzero. Then:

* every representation of `G` on `kⁿ` is semisimple;
* the weights of a simple representation form one `Γ`-orbit;
* every `Γ`-orbit is the set of weights of some simple representation;
* two simple representations are isomorphic if and only if they have the same weights;
* if `χ` is a weight of a simple representation `ρ`, the `k`-algebra of matrices
  intertwining `ρ` with itself is isomorphic to the subfield of `Ks` fixed by the
  stabilizer of `χ` in `Γ`.

This is a statement only; nothing is proved here. -/
def MultiplicativeTypeRepresentationGaloisOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom], IsMultiplicativeType G →
    ∀ (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks],
      haveI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k Ks)))
      let weights : {n : ℕ} → MatrixRepresentation G (Fin n) →
          Set (rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G)) :=
        fun ρ => {χ | (ρ.baseChange (algebraBaseMap k Ks)).characterSpace χ ≠ ⊥}
      let orbit : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G) →
          Set (rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G)) :=
        fun χ => Set.range fun σ : Ks ≃ₐ[k] Ks =>
          rationalCharacters.galoisRepresentation k Ks G σ χ
      (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
          ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} = ⊤) ∧
      (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible →
        ∃ χ, weights ρ = orbit χ) ∧
      (∀ χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G),
        ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          ρ.IsIrreducible ∧ weights ρ = orbit χ) ∧
      (∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
        ρ.IsIrreducible → σ.IsIrreducible →
          ((∃ C : Matrix (Fin m) (Fin n) k,
              ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin) ↔
            weights ρ = weights σ)) ∧
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
        (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G)),
        ρ.IsIrreducible → χ ∈ weights ρ →
          ∀ H : Subgroup (Ks ≃ₐ[k] Ks),
            (∀ σ : Ks ≃ₐ[k] Ks,
              σ ∈ H ↔ rationalCharacters.galoisRepresentation k Ks G σ χ = χ) →
            ∃ f : IntermediateField.fixedField H →ₐ[k] Matrix (Fin n) (Fin n) k,
              Function.Injective f ∧ Set.range f = {C | ρ.Intertwines ρ C}

end Langlands.GroupScheme
