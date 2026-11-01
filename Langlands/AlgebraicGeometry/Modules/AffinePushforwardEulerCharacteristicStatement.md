# Euler characteristic and actual affine pushforward

`AffinePushforwardEulerCharacteristicStatement` concerns an actual affine
morphism `h : X ⟶ Y`, a map `g : Y ⟶ Spec K` over an arbitrary field, and an
actual quasi-coherent module sheaf `M` on `X`. It asserts two conclusions:

- `M` has finite cohomology over `K` via `h ≫ g` if and only if the actual
  pushforward `h_* M` has finite cohomology via `g`.
- When these finiteness conditions hold, the actual integer Euler
  characteristics agree.

Here finite cohomology means that each actual right-derived cohomology
module is finite dimensional and that all sufficiently high degrees are
categorically zero, exactly as in `DerivedSections.HasFiniteCohomology`.
No properness or finite generation of `M` is assumed. The statement
transports finiteness; it does not assert it unconditionally.

This is derived content from two published Library results:
`affineQuasicoherentHigherDirectImageVanishing` supplies vanishing of all
positive higher direct images, and
`DerivedSections.pushforwardCohomologyIso` then identifies actual
cohomology of `M` with actual cohomology of its pushforward over the same
affine base. These are isomorphisms of `K`-modules. Finite dimensionality,
eventual vanishing, and the dimensions in the Euler sum are invariant
under these isomorphisms. This explains the full provenance without
introducing a new external-source assertion.

Every finite morphism is affine, so this result supplies the cohomology
comparison needed for finite-map numerical arguments. It does not assert
a Hilbert polynomial, a projection formula, multiplication by native
rank, or the polarized rank formula.
