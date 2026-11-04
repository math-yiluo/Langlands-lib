# Actual fppf images of represented subgroup products

This is an internal all-test transport construction for the published
`IsFppfImage` and `IsFppfProduct` predicates. It works over an arbitrary base
scheme at the ambient universe. No smoothness, connectedness, affineness,
normality, or field hypothesis is added.

`FppfLocallyInImage F q x` means that after one actual flat surjective locally
finitely presented morphism of relative test schemes, the point `x` lifts to
a point of the subgroup functor `F`. This is only a proposition, not a choice
of a cover or a sheafification construction.

For a supplied actual `IsFppfImage F E q`,
`fppfLocallyInImage_of_mem` constructs this cover by pulling back the fppf
homomorphism between the supplied subgroup representatives along a point of
the target representative. Its second projection supplies the required lift.
`mem_iff_fppfLocallyInImage` proves the converse by fppf descent of membership
in the monic target representative. `le_of_map_le` consequently places `E`
in any fppf-local subgroup containing the ordinary image of `F`.

`IsFppfProduct.of_fppfImages` transports a represented fppf-local ordered
product. Its hypotheses supply a source product `F N` represented by `i`,
actual fppf images `E` and `M` of the factors, an actual fppf image of `range i`
represented by `j`, and closedness of `j`. Its conclusion is exactly
`IsFppfProduct E M j`.

For the forward membership implication, a target point is first lifted
fppf-locally to `range i`. The source product presentation gives a second cover
and an ordered factorization there. Composing the two covers preserves
flatness, scheme surjectivity and local finite presentation. Applying the
ambient homomorphism to the factorization gives target factors in `E` and `M`.
For the reverse implication, `le_of_map_le` places both target factors in the
represented target image. The existing leastness lemma for local products
then descends membership along the factorization cover.

All proofs derive from the imported published all-test interfaces, standard
pullback stability and composition of the three fppf morphism properties, and
published monic-subgroup membership descent. There is no additional external
source claim. The result retains local rather than pointwise factorization on
the original test scheme.
