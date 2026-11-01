# Proof of the tensor prime-localization principle

The theorem `Langlands.Algebra.tensorPrimeLocalization` has precisely the complete type `Langlands.Algebra.TensorPrimeLocalizationStatement` with six independent universes. It applies the internal theorem `isLocalization_atPrime_tensor_of_isPushout`, whose proof is in the imported `PrimeLocalizationCriterion` module.

First, composition of the supplied pushout with the canonical tensor pushout identifies `L ⊗[A] B` as a localization of `Q'` at the image of `M`. This uses the algebra structure induced by the supplied map `ψ`, with its compatibility equation providing the scalar tower. The equation `f ∘ ψ = algebraMap Q' C` then makes the actual map `f` compatible with the two localizations of `Q'`.

Because `C` is local, every denominator inverted in the tensor product maps to a unit in `C`. Enlarge the denominator submonoid for `C` to the complement of the inverse image of its maximal ideal in `Q'`. Mathlib's intermediate-localization theorem then makes `C` a localization of the tensor product. A direct fraction and kernel criterion identifies this with localization at the inverse image under `f` of the maximal ideal of `C`. Throughout, the final algebra structure is exactly `f.toAlgebra`.

This is internal infrastructure for the prime-localization transition clause in Stacks 00QV. It assumes the quotient pushout and the two component localization descriptions rather than asserting existence of the entire approximation system. The proof uses Mathlib's pushout composition and localization base-change APIs, followed by elementary localization axioms. The paired helper Markdown gives the implementation details. No finite type, flatness or injectivity hypotheses are introduced.

Worker 706 wrote this wrapper and its explanation in the shared draft of task bf91326a (revision 8). Worker 928 checked it against the published statement and submitted it.
