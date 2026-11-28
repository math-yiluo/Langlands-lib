# Existence of the actual translated comparison

Module `Langlands.Representation.Plancherel.ActualConjugateLeviExistence`.

Fix a rational point `g` of the compact open subgroup `K`, write
`χg = χ ≫ Int(g)`, `Ag = conjugateRepresentation χ g A` and `Pg` for the
conjugate parabolic presentation `conjugatePresentation χ g K K _ P`. The
translated family `ActualParabolicUnitaryTranslation.ofCommonLevi` is a
common-Levi family `U` on the target side, preceded by the unitary translation
`unitaryTranslation`.

- `intertwiningComp_equiv_apply` and `ofCommonLevi_apply`: the translated family
  evaluates as `U (zg z) (unitaryTranslation … z v)`, where
  `zg = unitaryConjugateParameter χ g`.
- `ofCommonLevi_bijective`: when `U` satisfies
  `ActualCommonLeviV3.PreservesCoefficientsAndForms`, the translated family is
  bijective at every unitary parameter, being a bijection after an
  equivalence.
- `ofCommonLevi_coefficientMap` and `ofCommonLevi_formalDegreeForm`: for any
  inducing equivalence `E` such that the unitary translation is the actual
  product left translation followed by `coefficientCongr` along `E`, the
  translated family preserves the published coefficient map `coefficientMap`
  and, for compatible quotient Haar measures (`CompatibleHaar`), the published
  form `formalDegreeForm`. The proofs combine the preservation property of `U`
  with `coefficientMap_of_eq_translated` and `formalDegreeForm_of_eq_translated`.
- `ofCommonLevi_coefficientMap_unitary` and
  `ofCommonLevi_formalDegreeForm_unitary`: the same with `E` the unitary
  conjugate-twist comparison `unitaryTwistEquiv`, the hypothesis being
  `unitaryTranslation_eq`.
- `existenceLaw`: under the source normalization `HasSourceNormalization`,
  `ExistenceLaw` holds. For a rational point `g` of `K`, conjugate data `dg`
  and presentations `P`, `Q` with `CompatibleHaar`, the closed common-Levi
  coherence `ActualCommonLeviCoherence.closedCommonLeviCoherence` for
  `(χg, Ag, dg)` supplies a system of actual normalized comparisons. Its member
  from `Pg` to `Q` is the continuation `U`, and `ofCommonLevi` of `U` is the
  required actual comparison: it is presented by `U`, and the previous items
  give bijectivity and the coefficient and form identities.

The comparison formula and its regularity and coefficient properties are
in Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.3 formula (1) and Lemma V.3.1,
printed p. 295, PDF p. 61.
