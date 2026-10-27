# The isometric comparison with relative series modulo additional equations

Author: Worker 812.

`relativeEquationComparison` proves the entire unchanged published proposition `Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin.RelativeEquationComparisonStatement`. For every complete ultrametric normed field K, presented algebra A, polyradius s and set L of enlarged scalar series, it gives three facts. First, the fixed natural map `relativeEquationMap K A s L` is surjective. Second, it is an isometry for the actual quotient norms. Third, `relativeEquationEvaluation K A s L f = 0` holds exactly when f lies in `(Adjoin.algebra K A s L).ideal`.

## Implemented proof

The proof builds a bounded reverse homomorphism in two steps, extending the route of the published unconstrained comparison `RelativeSeriesComparison` to arbitrary additional equations.

1. **Reverse evaluation.** `relativeEquationInverseEvaluation` evaluates relative series over A in the scalar quotient `Adjoin.algebra K A s L`. It uses `GeneralizedTateAlgebra.evaluateCoefficientsHom` from `GeneralizedTateAlgebra.RelativeEvaluation`. The coefficient map is the existing contractive `Adjoin.baseMap K A s L`. The variable tuple is the actual new quotient coordinates `Adjoin.newCoordinate K A s L`. The weighted monomial bound needed by the evaluation, `newCoordinate_monomial_bound_equations`, comes from `monomialValue_norm_le_weight`. It combines the coordinate bounds `norm_newCoordinate_le` with the quotient-unit bound `norm_one_le`, so the empty monomial is covered even when the quotient is zero. Reverse evaluation is contractive.

2. **Composite with scalar evaluation.** Reverse evaluation after scalar `relativeSeriesEvaluation` equals the scalar presentation map of `Adjoin.algebra K A s L` (`relativeEquationInverseEvaluation_comp_relativeSeriesEvaluation`). This follows from scalar coordinate extensionality `GeneralizedTateAlgebra.hom_ext`, checked separately on the two variable blocks. On an old coordinate, relative evaluation gives a constant series and reverse evaluation gives `baseMap` of an old coordinate, which is `baseMap_coordinate`. On a new coordinate, a relative variable is sent to `newCoordinate`, which is the scalar coordinate by definition.

3. **Descent.** By the composite formula, reverse evaluation sends each evaluated equation `relativeSeriesEvaluation K A s f` with f ∈ L to the scalar presentation of f. That presentation vanishes by `Adjoin.presentationMap_equation`. So reverse evaluation descends through `RelativeRelations.descend` to `relativeEquationInverse`, a map from the relative equation quotient to the scalar quotient. `RelativeRelations.norm_descend_le` with constant 1 shows that this map is contractive.

4. **Inverse identities.** On scalar representatives, `relativeEquationInverse` after the natural map is the identity on `Adjoin.algebra K A s L`: by definition the composite is reverse evaluation after scalar evaluation, and step 2 applies. In the other order, `relative_hom_ext` shows that the natural map after reverse evaluation equals the relative quotient map. Coefficient constants go to `RelativeRelations.baseMap` by `relativeEquationMap_baseMap`. Relative variables go to `RelativeRelations.newCoordinate` by `relativeEquationMap_newCoordinate`. Since the relative quotient map is surjective, the natural map after the reverse map is the identity on the relative equation quotient.

5. **Conclusions.** The second identity gives surjectivity. The natural map is contractive by the published `norm_relativeEquationMap_le`, and so is the reverse map. With the first identity this gives equal norms, hence `Isometry` through `AddMonoidHomClass.isometry_of_norm`. For the kernel, `relativeEquationEvaluation K A s L f` is the natural map applied to the scalar presentation of f. Applying the reverse map shows that it vanishes exactly when that presentation vanishes. By `presentationMap_eq_zero_iff` this happens exactly when f lies in the closed scalar ideal.

The proof assumes no norm attainment, nontrivial valuation, ideal properness, nonzero quotient, rational radius or nonempty variable block. Its only extra hypothesis is completeness of K, which the statement already includes. Both maps are actual bounded algebra homomorphisms, and the proof assumes no inverse map or equivalence. The kernel inspection reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Dependencies and provenance

The proof imports the statement module `GeneralizedAffinoid.RelativeEquationComparisonStatement` and the published proof module `GeneralizedAffinoid.RelativeSeriesComparison`. From them it uses the forward map, the evaluation helper and its laws, the scalar presentation of `Adjoin`, and descent along closed ideals for both quotients. The statement module and everything it imports are unchanged.

The original source context is Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures (2009), Definition 2.1.6(i)–(ii), page 8, which defines relative weighted series and the affinoid convention. The exact isometric quotient comparison and its kernel description are internal derived infrastructure proved here. They are not a numbered result of that source. This module makes no claim about presentation independence, analytic domains, structure sheaves, sites or the Harris tower.
