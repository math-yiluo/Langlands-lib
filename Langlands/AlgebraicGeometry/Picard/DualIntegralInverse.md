# Exact inverse-multiple data for actual dual homomorphisms

This internal derived construction starts with the actual two integral maps in
`Rationalization.IntegralInverseData A B`. It uses the conditional dual abelian
schemes constructed from their universal Poincaré families, geometry and inverse
evaluations, together with the displayed tensor and Picard coherence inputs.
Additivity of dualization is required for endomorphisms of `A` and of `B`.

`dualIntegralInverseData` has forward map the actual dual of the original
reverse map and reverse map the actual dual of the original forward map. Its
common integer multiplier is exactly the original one. The proof reverses
composition under actual dualization, applies the two supplied integral
composite identities, then uses additive dualization to move the integer
multiple outside. The actual dual of the identity is the identity. No scalar
is inverted and neither dual map is replaced by a rational representative.

`dualIntegralInverseData_finiteEtaleIsogenies` applies the exact
inverse-multiple isogeny theorem to these constructed data. When the common
multiplier is positive and invertible in global sections of the base, both
actual dual maps are finite étale isogenies. It does not assume an isogeny
property of either dual map. The result concerns the two maps in the supplied
inverse-multiple data and leaves geometric polarization and representability
open; it does not assert the dual-isogeny theorem for an arbitrary isogeny.
