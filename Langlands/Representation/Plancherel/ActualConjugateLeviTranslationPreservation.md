# Coefficients and forms under the actual translation

Module `Langlands.Representation.Plancherel.ActualConjugateLeviTranslationPreservation`.

Fix a rational point `g` of the compact open subgroup `K`, write
`χg = χ ≫ Int(g)`, `Ag = conjugateRepresentation χ g A` and `Pg` for the
conjugate parabolic presentation. Every map considered here is the actual
product left translation
`CoefficientConjugation.leviCoefficientLeftTranslation` from the coefficient
fiber of `(χ, A, P)` at a full parameter `u` to the fiber of the conjugate of
the twist, followed by `ActualConjugateLeviTensor.coefficientCongr` along an
arbitrary inducing equivalence `e` from the conjugate of the twist of `A` by
`u` to the twist of `Ag` by a parameter `w`.

- `Langlands.Plancherel.representationFormalDegree_pullback` and its bundled form
  `representationFormalDegree_smoothPullback`: the Schur formal degree is
  unchanged by pulling back along a topological group isomorphism that matches
  the central subgroups and pushes one quotient Haar measure to the other. The
  proof compares the orthogonality integrals through the induced quotient
  isomorphism.
- `representationFormalDegree_conjugate` and
  `representationFormalDegree_conjugate_equiv`: for split-central quotient Haar
  measures compatible under conjugation (`CompatibleHaar`), an inducing
  representation and its actual conjugate, or any representation equivalent to
  that conjugate, have the same formal degree.
- `leviCoefficientMap_translated`: the composite preserves the compact
  probability coefficient map. The integrand of the translated section at `l`
  is the source integrand at `g⁻¹ l`, and the Haar probability of `K` is left
  invariant.
- `leviFormalDegreeProductForm_translated`: for compatible quotient Haar
  measures, the composite preserves the inverse-formal-degree product form.
  The compact product forms agree by
  `TranslatedCoefficientValue.leviProductForm_inner_translated_of_irreducible`,
  and the formal degrees agree by the previous item.
- `coefficientMap_of_eq_translated` and `formalDegreeForm_of_eq_translated`:
  at a unitary parameter `z`, any equivalence `T` of the published fibers that
  equals the composite for an inducing equivalence onto the twist at
  `unitaryConjugateParameter χ g z` preserves the published coefficient map
  `coefficientMap` and, for compatible quotient Haar measures, the published
  form `formalDegreeForm`.

Source: Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.3 formula (1) and Lemma V.3.1, printed
p. 295, PDF p. 61; compact Haar probability of I.1, printed p. 240.
