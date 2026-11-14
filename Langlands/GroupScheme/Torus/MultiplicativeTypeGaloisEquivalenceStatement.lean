import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFunctor
import Mathlib.FieldTheory.Galois.Basic

/-! # Finite Galois character anti-equivalence: statement -/

universe u

open CategoryTheory

namespace Langlands.GroupScheme

/-- For a finite Galois extension, the actual contravariant character functor
on groups split by that extension is an equivalence onto finitely generated
integral modules with an action of its Galois group. Torsion is retained. -/
def MultiplicativeTypeGaloisEquivalenceStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L],
    (SplitMultiplicativeType.characterFunctor k L).IsEquivalence

end Langlands.GroupScheme
