# Base change of actual relative scheme points

Author: Worker 208.

This derived construction supplies the point-carrier identification implicit in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed page 6, the base changes preceding Theorem 3.6 and the local
point spaces in (3.6.1). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Let `C → D → A` be compatible commutative algebra structures, with
`IsScalarTower C D A`, and let `X` be any actual scheme over `Spec C`.
`ringBaseChange C D X` is the actual scheme pullback, as an object over
`Spec D`, with structure map the second pullback projection.
`ringTestRestrictScalarsIso C D A` identifies the test spectrum `Spec A`
viewed over `Spec C` by the two structure maps. Its underlying scheme
isomorphism is the identity. The required equality follows from the scalar
tower equation for algebra maps and contravariance of `Spec`.

`ringPointBaseChangeEquiv C D A X` is an equivalence between the actual
`A`-valued points of `X` over `C` and those of `ringBaseChange C D X` over
`D`. It transports the standard `Over.mapPullbackAdj` hom-set equivalence
along the test-spectrum isomorphism. Its inverse composes the actual point
with the first pullback projection. The two forward-projection lemmas state
that the corresponding point projects to the original point and to the
structure map `Spec A → Spec D`, respectively; hence it is the usual
pullback lift. Naturality in `X` follows directly from the right-variable naturality
of the same pullback adjunction after reassociating the transported morphisms.

All rings, schemes and tests occupy the arbitrary common universe `u` used
by the existing `RingPoint` construction. There are no affineness,
finite-type, quasi-compactness, separation, local-ring or topology hypotheses.
The unit constructs the carrier equivalence and its specified projection and
naturality properties. It does not prove a comparison of point-space
topologies, construct global-field completions or adele rings, or instantiate
the local rings and model base changes of (3.6.1). Those remain obligations of
the parent program.
