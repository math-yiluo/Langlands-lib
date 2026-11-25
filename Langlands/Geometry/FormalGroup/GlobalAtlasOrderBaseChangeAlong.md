# Actual global-cover comparisons over supplied scalar structures

This module transports the actual `globalCoverBaseIso` comparison to a
supplied target algebra structure and scalar map. It uses the prior
`GlobalAtlasOrderBaseChange` construction and the published scalar-transport
machinery, with no new literature assertion.

`globalCoverBaseReAlgebraIso` takes an equality between the induced and supplied
scalar structures and a supplied scalar map whose underlying ring map is the
original structural map. Equality elimination reduces to one scalar structure;
extensionality identifies the two algebra maps. The result is the existing
actual global-cover coefficient-extension isomorphism. Its two coordinate
lemmas use the same equality elimination, followed by the actual prior chart
coordinate equations. Both complete formal maps retain identity series.

`globalCoverBaseAlongIso` applies this construction to the actual algebra
`coefficientTest f` of a supplied map `f` and the proved equality with the
supplied target scalar structure. Its source is exactly supplied-target
extension of the original restricted global order action. Its target is the
global action extended along that same `f` and restricted to the actual image
cover `f '' s`. The two direction equations specify the whole forward and
inverse formal coordinate series on every test chart. Both actual inverse
equations and full-order commutation are inherited from the actual transported
isomorphism. No point-functor equivalence is used as a formal-map witness.

The parameters retain arbitrary commutative rings `O`, `R`, `S`, a ring `D`
over `O`, a finite coordinate type, an actual global formal module/order action,
and an arbitrary principal cover generating the unit ideal. `R`, `S` and test
algebras share universe `v`; `O` and `D` may have separate universes. The cover
may be infinite and `f` may merge its generators. The varying-Nilp fixed-frame
comparison is a further construction.
