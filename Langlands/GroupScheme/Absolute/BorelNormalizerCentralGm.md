# The central multiplicative branch of Borel normalizer induction

This internal derived unit eliminates the two supplied quotient objects from
`BorelGmQuotients` using the exact existing
`NormalSubgroupQuotientStatement.{u}` as an explicit premise. It neither proves
that proposition nor proves the unconditional `BorelNormalizerStatement`.

Work over an algebraically closed field `k` in any universe `u`. Let `G` be
smooth and affine, let `i : B → G` be Borel, and let `z : Gm → G` be a central
closed subgroup with an actual factorization `zB : Gm → B`, `zB ≫ i = z`.

`exists_borel_quotients_of_central_gm` supplies smooth affine group schemes
`Q` and `BQ`, fppf quotient homomorphisms `q : G → Q` and `p : B → BQ` with
their respective all-test kernels `range z` and `range zB`, and an actual
Borel embedding `j : BQ → Q`. It proves the commuting square, smoothness
of both quotient projections, geometric connectedness of `q`, the cartesian
square, and the exact all-test identity `(range j).comap q = range i`.
Connectedness of `G` is unnecessary for this construction.

The implemented proof uses `IsCentral.range_isNormal` to prove that `range z`
is normal. The Borel immersion is monic, so `comap_range_of_factor` identifies
its inverse image with `range zB`. Normality therefore pulls back to `range zB`
by `IsNormal.comap`. The composite `zB ≫ i` is closed, which makes `zB`
closed. The original Borel is smooth by definition and affine because its
inclusion is closed into the affine group `G`. Applying the explicit normal
quotient premise to these two normal closed subgroups supplies `q` and `p`.
The construction in `exists_borel_of_fppf_gm_quotients` then gives all the
listed Borel and geometric conclusions.

With `G` connected, `normalizer_borelRange_eq_of_central_gm` proves that the
normalizer of the image of `B(k)` in `G(k)` equals that image, under the
smaller-group hypothesis of strong Lie-dimension induction. It applies
`normalizer_borelRange_eq_of_fppf_gm_quotient` to the quotient just constructed:
the quotient is smooth connected affine, and its Lie dimension is strictly
smaller because the quotient projection is smooth and kills the closed `Gm`.
The smaller-group normalizer conclusion pulls back through its exact Borel
inverse image.

The definition entry `borelPointOfCentralGm` chooses an actual `B(k)` point
over any ambient rational point normalizing the Borel image, with precisely
these explicit premises. `borelPointOfCentralGm_comp` proves that its image
is the original point. This choice uses the established membership in the
actual all-test represented range; it does not assert surjectivity on arbitrary
test points for an fppf cover.

The provenance is internal composition of the named Library constructions and
the still explicit normal quotient proposition. No independent literature
assertion is introduced. Existence of a central closed `Gm` inside the given
Borel and the other branches of normalizer induction remain separate.
