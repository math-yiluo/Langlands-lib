# Relative wave packets under Weyl conjugation

`RelativeWavePacketAssociationReductionStatement` is the implication from
`EisensteinFunctionalEquationStatement.{0}`,
`IntertwiningSquareIntegrableExpansionStatement` and
`EisensteinImaginaryContinuationStatement` to `RelativeWavePacketAssociationStatement`.
The theorem `relativeWavePacketAssociation_of_inputs` proves this implication. The
premises respectively supply the identity of the continued series, finite expansions
with square-integrable target vectors and coefficients holomorphic on the imaginary
axis, and a common holomorphy domain containing the imaginary axis for the target
series. All three premises apply to the supplied actual Levi and parabolic maps.

## Relative coordinates

For the given `IsWeylConjugation` and a retraction of the target Levi,
`exists_relativeWeylParameter_linearEquiv` restricts `realWeylParameter` to an
equivalence `relativeParameterSpace p ≃ₗ[ℝ] relativeParameterSpace q`. The full real
Weyl map is an equivalence by restriction of rational characters to the Levis,
pullback along the Levi isomorphism and extension of scalars to `ℝ`. Each relative
space is the kernel of restriction to the canonical split centre lifted through its
Levi, by `relativeParameterSpace_eq_ker_centralRestriction`. The two lifts commute
with the Levi retraction and inverse conjugation composite. To see this, compose with
`p` and use `IsWeylConjugation.comp_eq` and the fact that inner automorphisms fix the
canonical central torus. Pullback then identifies the kernels.

## Packet transport

Write the source packet in coordinates `e`, with inducing vectors `v j`, coefficients
`b j`, and continued series `E j`. For each `v j`, take the finite target family
`ψ j i` and coefficients `a j i` from the intertwining expansion. Enumerate all the
pairs `(j, i)` as one finite family and use imaginary continuation to choose the
series `E' (j, i)` on a common target domain. Set the target chart `e'` to the
composition of `e` with the relative Weyl equivalence. The equality `w(i e(x)) =
i e'(x)` gives the parameter in the functional equation at every coordinate `x`.
All the holomorphy-domain conditions hold there, so that equation expresses
`E j (i e(x))` as the sum of `a j i (i e(x)) * E' (j, i) (i e'(x))`.

Use `b j(x) * a j i(i e(x))` as the target coefficients. The second factor is smooth
by restriction along the real-linear inclusion into the full imaginary parameter
space. Each product has compact support by the support of `b j`. The finite-sum
identity makes the source and target integrands equal pointwise. Both charts have the
same coordinate domain and use the same `spectralMeasure n`. Thus the original
function `Θ` itself satisfies the target packet predicate. Its given almost-everywhere
representative `f` belongs to the generating set of `parabolicSpectrum` and hence to
its closed span.

## Provenance

- J. Arthur, *An introduction to the trace formula*, in Clay Math. Proc. 4 (2005),
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`,
  printed pp. 33–35 (PDF pp. 45–47), Weyl parameter isomorphisms and Theorem 7.2(a),
  equation (7.3). This gives the identity and imaginary-axis analyticity used in the
  packet argument.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein
  series*, Clay Math. Proc. 13 (2011),
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`, §2, printed
  pp. 311–312 (PDF pp. 320–321). The working hypothesis describes the finite-dimensional
  target space of square-integrable inducing forms for the intertwining family.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, §10.5, printed
  pp. 281–282 (PDF pp. 293–294), equations (10.22)–(10.24). These supply the relative
  imaginary parameter space and wave-packet integral on `[G]`.
