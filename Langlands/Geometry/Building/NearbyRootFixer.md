# Root fixers of nearby subsets in a facet closure

This internal supporting unit connects affine facet incidence to root and sharp
fixers in the supplied upper apartment. Its provenance is the existing affine
root sign formula, the AS4 filtration comparison in `ChamberFiltration`, and the
bounded finiteness theorem derived from the full integer-valued V6 data in
`IntegerAffineRootLocalFiniteness`.

For any real affine space and family of affine roots satisfying bounded
finiteness, `AffineRootSystem.eventually_mem_facetClosure_smul_vadd` proves that
the original point `x` lies in the facet closure of `t • v +ᵥ x` for all real
parameters sufficiently near zero. There is no topology or norm hypothesis on
the affine space. Only the parameter line has its usual real topology. The proof
separates the finite set of roots with `|ψ x| ≤ |ψ.linear v|`. Continuity of their
real affine value functions preserves every nonzero sign near zero. For the other
roots, `|t| < 1` and the affine value formula preserve the sign directly. Roots
vanishing at `x` already satisfy the closed-side condition.

Under AS4, if a subset `Ω` lies in the facet closure of `x` and contains `x`, its
depth-zero root fixer for each relative root equals that of `{x}`. One inclusion
uses the point `x` in `Ω`; the other uses the published filtration comparison
between a facet and its closure. Taking the supremum over relative roots gives
the same equality for sharp fixers. In particular, if `x` lies in the facet
closure of `y`, the root and sharp fixers of `{x,y}` equal those of `{y}`.
The definition `sharpFixerPairEquivSingletonOfMemFacetClosure` transports the
sharp-fixer group through this equality. Its multiplicative equivalence preserves
the underlying rational point, as the accompanying simplification theorem states.

For an arbitrary `IntegerValuationBuildingData`, connected reductivity and
maximal splitness provide opposite-factor pairs through the published rank-one
factorization theorem, so bounded finiteness applies. The existing theorem
`affineRoot_mem_or_two_smul_mem` supplies AS4. Consequently, along every apartment
translation line the two-point root fixers simultaneously agree with the
translated singleton root fixers near zero; their sharp fixers agree there too.

The results concern root and sharp fixers. They do not identify full pointwise
fixers or neutral integral-point subgroups. They do not prove special-fibre
parabolic images or the unconditional depth-zero opposite-factor statement.
