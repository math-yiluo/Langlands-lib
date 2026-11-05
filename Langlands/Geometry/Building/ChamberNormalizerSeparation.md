# Sharp normalizer separation from the sharp product range

This is an internal algebraic adapter for the sharp chamber decomposition.
Its inputs are the published affine normalizer separation theorem in
`Langlands.GroupScheme.Rational.BruhatOppositeCellReduction` and facet constancy
in `ChamberParahoricConstancy`. It does not supply a sharp factorization range.

For any field in universe `u`, an affine ambient group, a commutative group
scheme mapping to it, and a cocharacter, the first theorem considers a
normalizing rational point with an expression `n = v * z * u`, where `v` is
in the opposite Dynamic unipotent group, `u` is in the original Dynamic
unipotent group, and `z` centralizes the given commutative group. The torus
centralizer lies in the cocharacter centralizer and hence its parabolic, so
`z * u * z⁻¹` is still in the original Dynamic unipotent group. The point
`n * z⁻¹` normalizes the commutative group and is a product of opposite and
original unipotent points. The published
`normalizer_eq_one_of_unipotent_product` makes this point the identity,
proving `n = z`. Negation of the cocharacter is identified with inversion of
its multiplicative-group parameter.

For an actual `KPApartmentData D`, the next theorem assumes explicitly that
`D.sharpUnipotentProduct C x ν` has range `D.sharpFixer C` and that this fixer
equals `D.sharpFixer {x}`. It expresses every point of the sharp normalizer
at `x` as such a triple and identifies it with the central coordinate.
The reverse subgroup inclusion follows from the inclusion of centralizer
points in normalizer points. This proves
`D.sharpNormalizer {x} = D.sharpCentralizer {x}`.

The facet specialization uses the published sharp fixer constancy theorem,
with its explicit extended-affine-root premise, to supply the fixer equality
at any point of the facet. The primary definition
`sharpNormalizerCentralizerEquivOfSharpProductRange` packages that equality
as a multiplicative equivalence preserving the underlying rational point;
the final simp theorem records that preservation.

No genericity, root ordering, or reductivity premise is needed for the
algebraic separation step. The facet adapter retains the actual sharp
centralizer and normalizer subgroups and the explicit sharp triple range.
It proves neither that range nor the complete sharp or full chamber
decomposition, and makes no assertion about the full central factor
`Z(F)^0`. Its provenance is the indicated internal derivation, not a new
claim of an unconditional chamber decomposition.
