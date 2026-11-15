# Pullbacks and inherited descent data for canonical based parabolics

This internal adapter specializes `BasedBorelTransport` to arbitrary pullbacks
and the existing closed-subgroup descent-data constructor.

`BasedBorelTransport.baseChangeInclusion` pulls back a supplied coordinate-torus
inclusion and identifies its source with the coordinate split torus over the
new base. Its cocharacter theorem uses the published fixed-exponent
base-change equation to identify the canonical positive-coroot cocharacter
exactly. The representability theorem combines this equation with dynamic
parabolic base change and base change of represented subgroup functors.

Given maps from a common scheme to two arbitrary base schemes, and a supplied
`BasedCoordinateIso` between their normalized coordinate-torus inclusions,
`BasedCoordinateIso.pullbackParabolicIso` constructs an actual isomorphism
between the pullbacks of any supplied representatives of the original
canonical dynamic parabolics. The inclusion equation and
`range_pullback_parabolic_comp` compare the original pulled-back inclusions,
without coordinate-source normalizations. `range_pullback_torus_comp` removes
the source normalizations from the torus range equation using invariance of
range under precomposition by an isomorphism.

For an existing ambient `Descent.Datum`, assume one based coordinate comparison
between the two overlap pullbacks whose ambient isomorphism is exactly the
datum's overlap. For a supplied closed representative of the canonical dynamic
parabolic, `Descent.Datum.basedParabolicSubgroup` constructs its actual descent
datum. For a supplied closed coordinate-torus inclusion,
`basedCoordinateTorusSubgroup` constructs its actual descent datum. The two
compatibility theorems say the original inclusions are compatible with these
data. Both constructors use the all-test range equations above and the
published `Datum.closedSubgroup`: the inherited cocycles follow from the
ambient cocycle by cancellation through the closed inclusions.

There is no affineness, reducedness, quasi-compactness, or covering hypothesis
on the bases or the overlap in these adapters. In particular, pullbacks of
affine canonical Borel representatives along arbitrary overlap projections may
be used. The root index types are finite, and the two applications to a
single ambient datum use the same supplied coordinate root datum and base.
These constructors preserve supplied subgroup geometry; the module does not
prove the representatives are Borels or construct the ambient datum or the
based overlap comparison. It supplies descent data, not effective solutions,
and does not establish innerness or the host existence theorem.
