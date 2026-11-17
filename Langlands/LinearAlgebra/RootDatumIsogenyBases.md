# Compatible bases for root-datum isogenies

This internal derived module chooses compatible bases for any supplied
isogeny of finite reduced integral root data. The construction applies
to the full weight and coweight lattices, with no semisimplicity
hypothesis and with arbitrary permitted root factors.

For `f : RootDatumIsogeny p P Q`, `CompatibleBases f` consists of a
base of `P`, a base of `Q`, and the statements that both positivity and
simple-root membership correspond under `f.indexEquiv`. The definition
`compatibleBases` constructs this data.

The proof chooses a regular integral coweight of `Q` using
`RootDatumCoweightFace.exists_regular_refinement`. Its image under the
contravariant coweight map of `f` is regular for `P`: evaluation on
each root is a positive root factor times its corresponding nonzero
evaluation in `Q`. The published integral base construction supplies
bases adapted to these two regular coweights. Positivity corresponds
by the defining transpose and root-factor identities. The published
reflection criterion for simple roots then gives correspondence of
their supports through `mem_support_iff_of_coweight_signs`.

`CompatibleBases.simpleIndexEquiv` and `positiveIndexEquiv` restrict the
original index equivalence to the corresponding simple-root and
positive-root subtype indices. These equivalences use the original
root indices and do not change either root datum.

The provenance is composition of the imported integral coweight,
base and root-datum-isogeny chamber results. The construction asserts
no equality of corresponding Cartan entries, root factors or group
parametrizations, and supplies no ambient group-scheme homomorphism.
