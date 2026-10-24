# Canonical comparison with the actual base-changed dual scheme

This module constructs the canonical comparison

`(dualScheme A hA)_{S'} ≅ dualScheme (A_{S'}) hA'`

for arbitrary `b : S' → S`. The left side is the actual fibre product of
the original chosen dual parameter scheme. The right side can be any
chosen dual parameter scheme satisfying the existing actual
universal-family property for `A_{S'}`.

The single additional theorem input is
`universality : PicardZeroUniversalBaseChangeStatement`. The module first
applies it to the original Poincare family, proving universality of the
explicit `poincareFamilyBaseChange`. It also obtains
`hasDualScheme_baseChange`, whose existence witnesses are precisely the
base-changed parameter scheme and this family. This does not assert that a
subsequent classical choice made by `dualScheme` is definitionally that
witness; the comparison isomorphism handles choices explicitly.

`dualSchemeBaseChangeIso` uses the already proved uniqueness theorem for
actual universal Picard-zero families. The required rigidified pullback
coherence is supplied by its existing proved theorem. The comparison is
chosen from a unique-existence proof of compatible parameter isomorphisms,
not from arbitrary isomorphism data.

`dualSchemeBaseChangePullbackIso` witnesses compatibility: pullback of the
new chosen Poincare family along the forward comparison is isomorphic to
the explicitly base-changed original Poincare family, as a rigidified line
bundle. `dualSchemeBaseChangeIso_unique` proves that every parameter
isomorphism with this property is the constructed comparison. It makes
no uniqueness claim about the bundle-isomorphism witness.

Finally, `dualSchemeBaseChangeIso_hom` identifies the forward map with the
actual classifier of the base-changed family, by the existing classifier
uniqueness theorem. These are scheme isomorphisms over `S'`; compatibility
with reconstructed group operations and coherence for iterated base change
are not asserted here.

## Provenance and scope

This is internal, derived infrastructure. It specializes the published
universal-family uniqueness proof to the constructed Poincare pullback,
using the named base-change universality proposition as an explicit proof
input. All classification properties quantify every test scheme. No
representability, fibre stability, group structure or geometric theorem
is silently added. In particular, the input base-change universality
statement is not proved here, and the construction supplies no
unconditional relative dual existence theorem.
