# Universal perfect sections over a noetherian base: proof

Author: Worker 137.

`noetherianUniversalPerfectSections.{u}` proves the named noetherian-base
statement for actual line bundles on smooth proper affine-base families.
The scalar rings remain arbitrary commutative rings in universe `u`.

Properness makes the source quasi-compact over the compact affine base.
The proof chooses a finite ordered affine cover using the published
`Scheme.OrderedAffineCover.ofCompactSpace`. Smoothness supplies flatness.
Each actual line-bundle restriction trivialization becomes a
trivialization of ordinary module pullback along the open immersion,
using the inverse component of
`Scheme.Modules.restrictFunctorIsoPullback`.

The published `noetherianCechPerfectRepresentative` then supplies one
strictly perfect integer-indexed complex `K`, an original-base
comparison with the ordered Čech complex, and comparisons with the
pulled-back Čech complexes over every scalar algebra.
The proof retains this same `K` and its strict perfection.

Over the original base, the line bundle is quasi-coherent and the
structure map is separated, so
`CechResolution.nonempty_cechCochainComplex_iso` identifies its Čech
complex with its actual derived module sections. Composing that
comparison with the original-base representative comparison gives
the required original-base witness.

For each `φ : R ⟶ T`, the algebra structure is precisely
`φ.hom.toAlgebra`. Thus the scalar Čech statement's `specMap R T`
is the ordinary `Spec.map φ`, and its cover is the pulled-back
ordered affine cover. Local rank one is preserved by ordinary
module pullback, so the actual pulled-back coefficient is
quasi-coherent. The base-changed structure map is separated.
The same Čech-to-derived-sections theorem identifies the scalar
Čech complex with the required actual derived sections. Composing
with the supplied scalar representative comparison proves the
scalar clause for this one `K`.

This is an internal assembly of the published perfect Čech
representative, the Čech resolution comparison, quasi-coherence of
actual line bundles and their pullbacks, and the finite affine cover
constructor. It adds no naturality assertion and does not descend
the initial noetherian base hypothesis.
