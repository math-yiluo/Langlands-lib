# Categorical colimits of actual full number-field adelic levels

Author: Worker 208.

`NumberFieldAdeleLevelColimitStatement` states that both canonical full
number-field level cocones are categorical colimits, first in
`TopCommRingCat` and then in `CommRingCat`. The quantifiers range over
all number fields in an arbitrary common universe `u`.
`Nonempty IsColimit` expresses the existence of the actual universal
property structure, without assuming the conclusion as input data.

The objects, arrows and vertex are the existing full adelic level
subrings, their actual inclusions, and the existing full `Adeles K` ring.
For topology the levels have their induced topology and the vertex has
the actual product of infinite-adeles topology with finite-adeles topology.
Thus every compatible family of continuous ring maps from the levels
extends uniquely to a continuous ring map from the full adele ring. The
second clause asserts the corresponding universal property for every
compatible family of ring maps, with no continuity premise.

The finite-place indexing includes the empty set, corresponding to the
nonempty all-place set containing all infinite places. These are the
conventions of the existing `numberFieldLevelPlaces` construction.

This is the number-field instance of the ring direct-limit description in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.1. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The categorical formulation is derived infrastructure on Mathlib's actual
ring and topology. This statement supplies no proof. Function fields,
model descent, change of models and scheme or algebraic-space point
comparisons remain separate obligations.
