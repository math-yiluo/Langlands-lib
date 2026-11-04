# Enlarging the initial arithmetic model base

This derived construction implements the initial-set change used after equation
(3.5.1) in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.6. Conrad observes that increasing the initial
finite set has no impact on the direct limit. This file constructs the actual
full-adele point equivalence needed to compare the two initial model bases.

For finite sets `S ⊆ U` and an arbitrary scheme model `X` over the original
outside-`S` integer ring, `curvePlaceFixedModelInitialSetEquiv` identifies its
full-adele points with full-adele points of its actual pullback to the
outside-`U` integers. `numberFieldFixedModelInitialSetEquiv` gives the same
construction for the full number-field adele ring, retaining every infinite
factor. Both equivalences are the actual pullback-adjunction equivalence
`ringPointBaseChangeEquiv`, with the original diagonal scalar actions and the
literal inclusion of integer rings. The scalar tower is proved by equality of
these original maps; neither action is replaced.

The inverse point projects to `X` by the first pullback projection. The forward
projection identity follows from that formula and the equivalence inverse law.
These are intrinsic construction laws, not an assumed equality of models.

No finite-type, separatedness, finiteness of the constant field or nonempty-set
hypothesis is needed. The common universe is arbitrary. This file constructs
set equivalences; the comparison of the independently defined final topologies
and independence from a choice of spread remain subsequent proof obligations.
