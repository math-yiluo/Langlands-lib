import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Semisimplicity through complements of codimension one (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **For a group without characters, semisimplicity is tested on submodules of codimension
one** (Milne, *Algebraic Groups* (2017), Lemma 22.40). Let `G` be an affine group scheme of
finite type over a field `k` whose only character `G → 𝔾_m` is the trivial one. Then the
following are equivalent:

* (a) every finite-dimensional representation of `G` is semisimple;
* (b) every subrepresentation of codimension one of a finite-dimensional representation has a
  complementary subrepresentation;
* (c) every simple subrepresentation of codimension one of a finite-dimensional representation
  has a complementary subrepresentation.

Representations are matrix representations on `kⁿ`. As in Milne's Definition 4.15, a
representation is semisimple if it is the sum of its simple subrepresentations. Milne's section
assumes characteristic zero; the lemma and its proof do not use it, and the statement here
does not assume it. -/
def SemisimpleRepresentationCodimensionOneStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    Subsingleton (G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp) →
    let IsSimpleStable : {n : ℕ} → MatrixRepresentation G (Fin n) →
        Submodule k (Fin n → k) → Prop :=
      fun {n} ρ W => ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W
    let HasStableComplement : {n : ℕ} → MatrixRepresentation G (Fin n) →
        Submodule k (Fin n → k) → Prop :=
      fun {n} ρ W => ∃ W' : Submodule k (Fin n → k), ρ.IsStableSubspace W' ∧ IsCompl W W'
    [∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), sSup {W | IsSimpleStable ρ W} = ⊤,
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (W : Submodule k (Fin n → k)),
        ρ.IsStableSubspace W → Module.finrank k W + 1 = n → HasStableComplement ρ W,
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (W : Submodule k (Fin n → k)),
        IsSimpleStable ρ W → Module.finrank k W + 1 = n → HasStableComplement ρ W].TFAE

end Langlands.GroupScheme
