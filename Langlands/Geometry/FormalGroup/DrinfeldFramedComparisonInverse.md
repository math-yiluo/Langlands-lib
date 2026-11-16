# Actual inverses of framed formal comparisons

This internal module constructs an actual inverse of each specified
`DrinfeldFramedAtlas.Comparison`. Both triples retain the same fixed
`Nilp` object and supplied height-certified frame, local field, central
division algebra, embedded subfield and residue field. Principal
covers may differ and may be infinite. All universe restrictions of
`DrinfeldFramedComparison` remain.

`globalFrameQuasiIso_symm` proves that the identity frame comparison
forced by the reversed residue-map equality is the inverse of the
original identity frame comparison. It eliminates equality after
exposing the two stored residue maps. `globalFrameQuasiIso_map_symm`
extends this equation to the actual coefficient test algebra.

`reducedComparisonOnChart_symm` uses precisely the inverse coordinate
isomorphism on the same two finer covers with their roles exchanged.
Rationalization and chart evaluation preserve inversion, so its actual
quasi-isogeny is the inverse of the original chart quasi-isogeny.

`ReducedFramingSquare.symm` evaluates the original square on the
matching finer chart and reverses the two vertical quasi-isogenies
using `QuasiIsogeny.square_reverse`. The two preceding inverse
equations identify the resulting maps with those of the reversed
square. The proof compares entire full-order rational
quasi-isogenies. `FramingSquare.symm` also uses the actual identity
that quotient reduction preserves inversion of the specified formal
comparison, from `SpecialAtlasComparisonInverse`.

`Comparison.symm` retains this reversed target comparison, the
reversed residue equality, and the proved reverse framing square.
Inverting twice gives the same comparison, including its specified
formal map. Its target point-functor map is the inverse of the
original specified complete-family equivalence.

The provenance is internal, combining the actual comparison and
quotient-extension definitions, coefficient-extension inverse laws
and the actual rational square calculus. No representing object,
universal object or arbitrary equivalence of point functors is
supplied. Reflexivity, transitivity, framed isomorphism classes,
varying-base functoriality, group actions and representability remain
separate obligations.
