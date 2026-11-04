# Actual adelic levels over a fixed model base

This derived construction implements the fixed-model presentation on the left
of Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), equation (3.5.1), printed p.6. It uses actual arithmetic rings and actual
relative scheme points. The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`.

`AdelicLevelIndexAbove S` consists of the finite sets containing the initial
finite set `S`, ordered by inclusion. Union gives a common upper bound and
parallel arrows are unique, so this is a nonempty filtered category.

For a curve-place system over arbitrary fields `k` and `F`, or a number field
`K`, each actual adelic level at `T` is an algebra over the fixed outside-`S` integer ring through the
literal integer inclusion and the original `T` diagonal. Literal level
inclusions respect these scalar actions and form the coefficient diagram.
The number-field rings retain every infinite-place completion, so this is a
full-adele construction, including when the finite set `S` is empty.

For any scheme `X` over the fixed integer base, the published pullback-adjunction
equivalence identifies its points over this coefficient algebra with the points
of the actual model pulled back to `T`-integers, evaluated on the original
`T`-level ring. Its inverse is the actual first pullback projection.
The topology on the fixed-base points is induced from the original
`T`-model point topology along this equivalence, making it a homeomorphism.
The resulting point diagram and its quotient type with the final stage topology
use the existing generic `FilteredRingPoints` and `FilteredRingPointTopology`
constructions.

This construction needs no finite-type, affineness, separatedness, finite
constant-field or nonempty-initial-set assumption. It does not yet assert
compatibility with changing-level transitions, a coefficient-colimit universal
property, bijectivity onto adelic points, or model independence. Those are
separate obligations.
