# Actual changes of level for adelic model points

This module constructs the original change-of-level map for arbitrary actual
models over S-integer rings. It retains an arbitrary common universe, all
finite sets S and T with S contained in T, arbitrary fields k and F with an
algebra k to F for the curve-place family, and every number field K for the
full number-field family. Every infinite number-field factor remains present.
No finiteness, affine or separation hypothesis on the model is needed for
these constructions.

For curve places, `curvePlaceSIntegersMap` is the literal inclusion of
elements integral outside S into elements integral outside T. For number
fields, `numberFieldSIntegersMap` is the corresponding inclusion of
Mathlib's original S-integer subrings. Their coercion lemmas show that both
maps leave the underlying field element unchanged.

The two `AdeleLevelDiagonal_natural` identities prove that these base-ring
inclusions commute with the original S-integer diagonals and the actual
adelic-level inclusions. Thus they give commutative squares of the actual
rings and their original scalar maps. No T-integer action on the S-level
ring is imposed.

`curvePlaceLevelModelBaseChange` and
`numberFieldLevelModelBaseChange` are actual scheme pullbacks along the
spectrum of the respective integer inclusion. Their transition maps take
an actual S-level point, precompose its underlying scheme morphism with
the spectrum of the actual adelic-level inclusion, and lift this morphism
together with the original T-integer structure map into that pullback.
The diagonal compatibility identity proves the required pullback square.
The two projection lemmas for each family identify these first and second
projections exactly. In particular, the target is the base-changed model
over T-integers, with points taken over the actual T-level ring.

This is a derived construction of the maps used in the final part of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Theorem 3.6, printed p.6, and its proof on p.8.
There the source and target
models are finite type and the paper's global-field conventions apply.
The ring inclusions and pullback universal property define the same maps
without those restrictions, explaining the broader construction here.
The implementations use the published `CurvePlaceAdeleRing`,
`NumberFieldAdeleLevel` and actual `RingPoint` constructions.

Continuity, openness, separated injectivity, identification with products
of local coefficient maps, composition across several levels, model descent,
model independence and the global adelic colimit are separate obligations.
This construction asserts none of those further properties.
