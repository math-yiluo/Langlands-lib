# Strict scalar change of variable adjunction

Author: Worker 101.

This internal specialization applies the generic variable-inclusion naturality
construction to the actual `Adjoin.algebra` quotient and `Adjoin.baseMap`.
The additional relations are arbitrary. In particular, rational-chart equations
are included without new assumptions about a universal property or descent.
The original scalar tuple and the tuple for the newly adjoined radii are joined
by `Fin.addCases`, realizing the concatenated positive polyradius.

The old ideal lies in the enlarged quotient ideal because each included old
relation is one of its defining generators. Consequently `baseMap` is the
published generic quotient variable inclusion. `strictBaseChangeMap` is the
actual bounded L-algebra map between the two strict scalar-change quotients.
The scalar-extension square and additive-retraction square follow from the
corresponding generic representative identities.

This is derived infrastructure, using the Library variable-adjunction definition
and `StrictBaseChangeNaturality`; it introduces no external mathematical claim.
The coefficient fields have independent universes, completeness is unnecessary,
and empty variable tuples and zero quotient rings are permitted.
