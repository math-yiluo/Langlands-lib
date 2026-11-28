# Evaluation and coefficients of the inverse product left translation

Module `Langlands.Representation.Plancherel.TranslatedCoefficientInverse`, in
the setting of two semidirect decompositions `P = M ⋉ U`, `Q = N ⋉ W` of a
locally compact nonarchimedean group related by conjugation by `g`.

- `leviCoefficientLeftTranslation_eval`: the actual product left translation
  `CoefficientConjugation.leviCoefficientLeftTranslation` sends a product
  section `f` to the section whose value at `x` is the conjugated coefficient
  value (`conjugateValue`: same vector, same underlying functional) of `f` at
  `(g, g)⁻¹ x`. The proof checks pure tensors through the product-induction
  tensor equivalence, as for `translatedProduct_eval`.
- `leviCoefficientLeftTranslation_symm_eval`: the inverse translation evaluates
  at `x` as the inverse conjugated value at `(g, g) x`.
- `conjugateValue_contraction`: the conjugated value has the same contraction
  of vector against functional.
- `integral_leviIntegrand_inverseTranslated`: for `g` in a compact open
  subgroup `K` and any inducing equivalence `e`, the transport
  `coefficientCongr e` followed by the inverse translation preserves the
  `K`-integral of the diagonal contraction. The integrand at `l` equals the
  original integrand at `g l`, and the Haar probability of `K` is left
  invariant.
- `leviCoefficientMap_inverseTranslated`: consequently the same composite
  preserves the compact probability coefficient map
  `CompactInduction.leviCoefficientMap`, for any admissibility proofs on the
  two sides; both maps are the pointwise integrals of the previous item, by
  `CompactInduction.leviCoefficientMap_integral`.

- `untwist_conjugateValue_of_eq`: if an inducing equivalence `e` from the
  conjugate of a twist to a twist of `B` acts on vectors as a fixed equivalence
  `ι` from the conjugate of the untwisted representation to `B`, then removing
  the twists turns the value transport along `e` after conjugation into the
  fixed transport along `ι` after conjugation. Vectors agree by hypothesis;
  smooth functionals agree because `e⁻¹` and `ι⁻¹` agree on vectors.
- `untwist_inverseTranslated_eval`: suppose the inducing equivalence `E` onto
  the conjugate twist has the underlying linear map of `ι.symm`.
  For `coefficientCongr` along `E` followed by inverse product left translation,
  the conjugated untwisted output at `x` is `productCoefficientLeviEquiv ι.symm`
  of the untwisted input at `(g, g) * x`. The proof combines the evaluation
  rule for inverse translation with `coefficientCongr_eval` and inverts
  the untwisting identity for the forward equivalence.

These are the compact-probability coefficient identities used for the
comparisons of Waldspurger, *La formule de Plancherel pour les groupes
p-adiques* (2003), V.3 formula (1), printed p. 295, PDF p. 61.
