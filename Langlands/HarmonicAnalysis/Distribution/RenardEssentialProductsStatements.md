# Renard II.3.13: the three essentially compact convolution algebras

This statement unit covers the Lemma and its product construction in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.3.13, printed pp.54–55 / PDF pp.60–61. The group is any
Hausdorff locally compact totally disconnected topological group, in any
universe, with its Borel measurable structure and a left Haar measure.
No countability or unimodularity is assumed.

All declarations are in
`Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts`.
They are propositions about the existing `rightEssentiallyCompact μ`,
`leftEssentiallyCompact μ` and `essentiallyCompact μ`, which are submodules
of the original full complex algebraic dual `Distribution G`. The unit
constructs no replacement carrier and installs no unproved ring instance.

`AlgebraLaws μ S p` specifies the laws of a complex bilinear product on an
existing submodule `S`. Bilinearity is part of the type of `p`. The
proposition requires associativity, a two-sided unit whose underlying
distribution is the actual `dirac 1`, extension of the published compact
distribution convolution, and agreement with both published full Hecke
actions. The compact and Hecke lifts are constrained to equal their actual
underlying distributions; they cannot be unrelated representatives.
Together these laws express a unital associative complex algebra with the
submodule's existing addition and scalar action.

`RightProductSpecification` adds the formula used in the Lemma's proof.
For every test `f` and every compact-open subgroup `K` whose normalized
distribution `e_K` satisfies the scalar identity `f * e_K = f`, it requires
an actual Hecke element `h` with density `U * e_K`, and specifies
`(p T U)(f) = (T * h)(f)`. Here the first scalar identity uses the actual
`rightConvolveTest`, and the actions on distributions use the published
`rightHeckeConvolution`. The normalized Hecke element is the existing
`HeckeAlgebra.normalizedIndicator`; its identification with normalized
subgroup Haar is the separate published `RenardHecke.NormalizedIndicatorStatement`.
The formula is asserted for every permitted `K`, expressing independence of
the choice. The specification also includes
`(T * U) * h = T * (U * h)` with an actual Hecke representative for `U * h`.

`LeftProductSpecification` is the analogous source construction with left
and right interchanged: when `e_K * f = f`, it uses the Hecke density
`e_K * T` to evaluate `(p T U)(f)`. It also specifies the corresponding
left-action associativity identity. Its `leftHeckeConvolution` is the
published action using the inverse Haar measure in its transpose kernel,
so the nonunimodular case retains the required correction.

`TwoSidedProductSpecification` requires algebra laws on the actual
intersection and equality with both products under the inclusions of the
intersection into the two one-sided submodules. This is the substantive
agreement checked at the end of the Lemma's proof on printed pp.54–55.

`Statements` asserts existence and uniqueness of the right and left
products with these specifications, then existence and uniqueness of the
compatible product on the intersection for every such pair of products.
Uniqueness is an explicit internal formulation of the source's
choice-independent defining formulas. These formulas determine the
products on all tests by compact-open local units, as in the source;
existence includes the stated Hecke witnesses and algebra laws.

The targets have no proofs in this unit. The identification of the right
algebra with the actual idempotented-ring completion, and the categorical
center comparison, are separate obligations.
