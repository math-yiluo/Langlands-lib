# Centered gamma germs from a reflected ratio

This internal adapter joins `TemperedLFactorGamma.ReflectedRatioData` to the
centered segment family gamma germ. It uses the actual certified block
polynomials and does not require either polynomial of the whole induction to
equal its block product.

`HasRationalGammaExpression δ P Pd G` means that there exist a nonzero complex
coefficient `c` and an integer exponent `m` such that `G` is the Library's
`rationalGammaExpression δ c m P Pd`. It asserts a rational function identity;
it contains no assertion that the polynomials or the rational function satisfy
any representation-theoretic factor relation.

The reflected-ratio datum says that `B/reflected(Bd)` equals
`cr X^ar P/reflected(Pd)`. The first proof absorbs this discrepancy by replacing
the epsilon parameters `(c,m)` with `(c/cr,m-ar)`. It uses the existing nonzero
rational epsilon unit, integer-power subtraction, and field algebra. No
polynomial cancellation or nonvanishing hypothesis is needed for this rational
identity. `HasRationalGammaExpression.of_reflectedRatio` packages its
existential consequence.

The arbitrary-rank inverse-transpose certificate lemma reduces positive
successor ranks to the published Gelfand--Kazhdan equivalence in
`SmoothDualPairFactors`. At rank zero both factor relations are false.
`centeredSegmentFamilyLProduct_of_inverseTransposeCertifiedProduct` applies
this equivalence to the real determinant twist of each supplied block and the
actual smooth dual of another such block. Admissibility and irreducibility of
the twists and their smooth duals follow from the published twist and compact
open duality theorems. The existing dual-product theorem then uses admissible
biduality, reverses the pair order, and transposes the finite product.

`centeredSegmentFamilyGammaGerm_of_reflectedRatio` builds the two Appendix
L-products from the original and inverse-transpose block certificates, absorbs
the supplied ratio datum, and applies the existing punctured-neighborhood gamma
theorem. Each dual block polynomial is nonzero by its actual certificate, so
their finite product is nonzero. The conclusion existentially retains the
adjusted epsilon coefficient and exponent.

All assertions are derived from the imported Library interfaces. This file
does not introduce a new assertion from original literature. The caller still
supplies the segment-head and equal-rank supercuspidal factor statements,
admissibility and irreducibility of the blocks, all actual block certificates,
the rational gamma formula, and the reflected-ratio datum. It neither proves
classification exhaustion nor discharges the global associated-pair gamma
comparison or the real-axis order restriction required for the host induction
theorem.
