# Local components of a cuspidal summand detected by compressed traces

The module concerns `GL_{r+1}` over a number field `K` with compact adele quotient, the actual
almost-everywhere cuspidal subspace `S` of `L²` of the positive rational quotient, and a
cuspidal operator realization `R` with a linear map `Φ` sending each of its vectors to the
`L²` class of the function it induces (`IsGeneralLinearFormClass`).

## Unitary central character

`hasUnitaryCentralCharacter_of_formClass` proves that such an `R` has unitary central
character. By `existsUnique_hasCentralCharacter`, `R` has a central character `χ`. For a
nonzero vector `f` and a nonzero scalar `a` in a finite completion `K_v`, the scalar matrix of
`a` acts on `f` by `χ_v(a)` (`finiteIdeleInclusion_mem_centralCharacterSubgroup_iff`). The class map is injective
(`RealizationSummand.classMap_injective`) and carries the finite adelic action to right
translation on `L²` (`RealizationSummand.classMap_finite`), which is isometric
(`norm_fullAEL2CuspidalBoundedRightAction`). Hence `|χ_v(a)| = 1` at every finite place. The
idele subgroup where `|χ| = 1` is closed and contains the principal ideles and each embedded
`K_vˣ` for finite `v`, so it is everything by `IdeleDensity.eq_top_of_isClosed`. The last step follows
`CuspidalOperatorRealization.hasUnitaryCentralCharacter_of_isUnitarizable`, using the `L²` norm.

## Local characters

`exists_distribution_ne_zero_of_compressedTrace` takes an irreducible closed invariant
subspace `P` of `S` containing the image of `Φ` and a spectral presentation `D` of `R` whose
component at a finite place `v` is irreducible and admissible. Let
`f(g) = φ(g_v) f^v(g)` with `φ` locally constant compactly supported on `GL_{r+1}(K_v)` and
`f^v` invariant under the points at `v`. If the compression of `R_S(f)` to `P` is trace class
with nonzero trace, then the distribution character of the local component of `D` at `v` does
not vanish at `φ` for some Haar measure.

By `presentedLocalComponentHilbertOccurrence` the local component occurs in `P`.
`IsotypicTrace.cuspidalIsotypicTraceFactorization_of_occurrence` then writes the compressed
trace as the local character at the pullback of `φ` to the local group-scheme points times a
functional of `f^v`, so the local character there is nonzero. `BaseChange.distribution_comp_equiv`
transports this along `localGLHomeomorph` to the matrix group `GL_{r+1}(K_v)`, with the
pushed-forward Haar measure.
