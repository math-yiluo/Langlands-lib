# Pulling back a representation of the full Isom presheaf

Worker 220.

This internal adapter combines the published `LocalGroupIso.presheaf`,
`GroupIsomorphismScheme.baseChange`, and the conversions between presheaf
representations and `GroupIsomorphismScheme`. It imposes no restriction
on the base morphism or on the group schemes.

Given a representation of the full Isom presheaf by an actual relative
scheme `P`, `representableByBaseChange` represents the presheaf of the
base-changed groups by the actual categorical pullback
`(Over.pullback b).obj P`. It constructs the old universal family from
the representation, applies the published representing-scheme
base-change construction, and returns its presheaf representation.

`representableByBaseChange_homEquiv` verifies that classification at
every parameter point is the composite of the parameter pullback
adjunction, the old classification equivalence, and the all-test family
base-change equivalence. The proof uses the refinement formula for the
pulled-back universal family and the original representation's
naturality at the identity.

Every test is an arbitrary relative scheme in universe `u`. This
construction transports a supplied representation; geometric existence
of a representative remains a separate proof obligation.
