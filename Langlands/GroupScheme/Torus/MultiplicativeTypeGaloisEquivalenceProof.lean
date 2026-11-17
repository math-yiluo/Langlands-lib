import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisEquivalenceReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessProof

/-! # Finite Galois character anti-equivalence: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Finite Galois character anti-equivalence for groups of multiplicative type**
(derived from Milne, *Algebraic Groups* (2017), Theorem 12.23): for every finite Galois
extension `L/k`, the actual character functor on groups split by `L` is an equivalence
onto finitely generated integral modules with an action of `Gal(L/k)`. -/
theorem multiplicativeTypeGaloisEquivalence :
    MultiplicativeTypeGaloisEquivalenceStatement.{u} :=
  multiplicativeTypeGaloisEquivalence_of_fullFaithfulness
    multiplicativeTypeGaloisFullFaithfulness

end Langlands.GroupScheme
