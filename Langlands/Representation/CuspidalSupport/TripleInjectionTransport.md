# Actual triple injection transport

This internal unit transports actual injections through equality of ranks
and between the two three-factor bracketings. It retains the supplied
topological data and independent field and representation universes.

`Parabolic.leftProductMap` fixes the first smooth factor of a positive
two-block normalized product and applies a supplied actual intertwiner
to its second factor. Its Levi map is the external tensor of the identity
and that intertwiner. `leftProductMap_injective` applies the existing
injectivity theorem for the actual indexed tensor map, then injectivity
of normalized parabolic induction. There is no irreducibility,
admissibility or equal-rank hypothesis in this map construction.

`rankPullback F T h` pulls an actual smooth representation of
\(\mathrm{GL}_n(F)\) to \(\mathrm{GL}_m(F)\) along the entry-preserving
`reindex (finCongr h)`, for \(h:m=n\). Its representation carrier is the
original one. Continuity of that explicit group equivalence supplies
smoothness. Equality elimination proves that this pullback preserves
irreducibility. `rankPullbackMap` preserves the original linear map, and
`rankPullbackMapReflect` recovers its original intertwining law by applying
the pulled-back law to the inverse image of a group element. Reflection
also preserves injectivity, since its underlying function is unchanged.

`uniformRightInductionEquiv` applies the existing exact
`threeBlockRankCastEquiv`. It identifies the rank pullback of the literal
three-block induction at \(d+(d+d)\) with the literal right-bracketed
three-block induction at \((d+d)+d\), along `Nat.add_assoc d d d`.
The supplied three factor objects and their order are unchanged. Its
carrier universe is `max uF uV`.

`uniformTripleOccurrence_of_rightInductionInjection` takes an actual
injection from the pulled-back irreducible ambient object into that
right-bracketed induction. Compose with the inverse of the preceding
equivalence, reflect the resulting intertwiner to the original ambient
rank, and retain injectivity. The already proved uniform
injection-to-Jacquet-occurrence theorem then gives the actual supplied
three-factor cuspidal tensor as a subquotient of the normalized Jacquet
module of the original ambient object.

The provenance is internal: indexed tensor injectivity, actual induction
maps, entry-preserving group reindexing, existing normalized induction in
stages, and the previously proved first-adjunction occurrence interface.
This unit proves no local repeated-factor transfer on its own.
