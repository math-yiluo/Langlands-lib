# The actual replacement quotient of the negative-inner outer source

This module identifies a concrete surjective exact map out of
the mixed source in the negative-inner two-piece filtration. It does not assume
that the filtration map factors through this quotient.

For linked `d,e,k` with negative signed inner weight `H`, use the quotient
parities and endpoint characters of `RealInducedPairNegativeInnerQuotient`:
`h=H.natAbs`, `sd=(h+L)%2`, `u=lo d sd`, `v=hi d sd`, `x=lo e 0`, `y=hi e 0`.
The source is the actual list
`[x,induced(pairInduced u y P),v]`, namely the mixed outer piece in
`RealInducedPairNegativeInnerFiltration.filtration_of_pieces`.

`RealInducedPairNegativeOuterQuotientStatement` quantifies every such linked
negative-inner pair and asserts existence of a complex-linear surjective exact
intertwiner from this mixed source to the actual
`RealInducedPairLinkedReplacement.replacementPair d e k`.
`realInducedPairNegativeOuterQuotient` proves it. No outer-square inequality
or original parity hypothesis is imposed.

The outer datum `pairInduced u y P` is exactly `outerData d e k`. The character
`x` is interlaced inside its endpoints, with positive distance `L-h<P` from
the lower outer endpoint. The published interlaced character-induced
equivalence, extended through the final character `v` by induction in stages,
therefore gives an exact equivalence `exposeEquiv` to
`[induced outerData,character x,character v]`.

Now `v.exponent-x.exponent=h` and the chosen signs satisfy the rank-one tail
parity. Apply the actual tail on this final ascending pair. It surjects onto
`[induced outerData,induced(pairInduced x v h)]`, as verified by its explicit
inverse-tail section. The second induction datum has the same absolute weight
and exponent as the signed `innerData d e k`, so the underlying standard
module equals that of the actual replacement pair.
`replacementQuotient` is the composition of the reordering equivalence, this
tail, and equality transport. Its exactness and surjectivity follow from
those three actual constructions.

`ker_replacementQuotient` gives its exact kernel. It is the range of the
inner binomial map at cutoff `h` in the exposed list, pulled back along
`exposeEquiv`. This is the published tail-kernel/range identity with the
outer induction block retained.

To finish the negative-inner filtration through this source, one must
prove that its mixed-source filtration map sends this kernel into the earlier
swapped-pair range. This module supplies neither that kernel-image assertion nor
the unrestricted filtration; the Library completes the negative-inner case as
`realInducedPairFiltration_of_negativeInner` in
`RealInducedPairNegativeBraidFiltrationClosure`.
