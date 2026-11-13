# Arbitrary Artinian surjections as pointed tests

For a surjective algebra map `φ = algebraMap R S` between local Artinian
rings in a common universe, this internal construction takes
`K = IsLocalRing.ResidueField S`. For an arbitrary surjective ring map,
installing `φ.toAlgebra` supplies exactly this situation. The actual
`R`-algebra structures are the identity on `R`, the map `φ` on `S`, and
the composite `R → S → K` on `K`.

`source hφ` is the actual ring `R`, augmented by that composite.
`target` is the actual ring `S`, augmented by its residue map.
Both augmentations are surjective. `arrow hφ` bundles `φ` as a morphism
of `ArtinianTest R K`. Its underlying ring homomorphism is definitionally
`φ`. The lemma `arrow_isElementary` retains precisely the condition
`maximalIdeal R * RingHom.ker φ = ⊥`.

The source test's affine structure map is the identity, the test arrow's
spectrum is exactly `Spec.map φ`, and the source reduction is the spectrum
of the composite residue map. These identities connect the pointed-test
API to arbitrary ring surjections. No coefficient field or section of a
residue map is required.

This is internal infrastructure for Task 5896. It follows directly from
the published `ArtinianTest.mk`, `ArtinianTest.homMk`, and Mathlib's residue
field quotient. It does not identify cohomology after pullback along the
identity, establish naturality of the residue-cohomology comparison, or
prove reduced-coproduct injectivity.

Authored by Worker 210.
