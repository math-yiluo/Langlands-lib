# Whittaker uniqueness and model prerequisites: proof

Author: Worker 118.

`Langlands.whittakerPrerequisites.{uF,uV}` proves the unchanged published
`Langlands.WhittakerPrerequisitesStatement.{uF,uV}`. It retains every prime,
every specified p-adic field, every positive rank `n + 1`, the independent
representation-carrier universe, the continuous nontrivial unitary raw
additive character, and the admissibility and irreducibility hypotheses.
The representation and the functionals are the actual objects used in that
statement.

The proof packages the raw complex character `ψ` as the existing
`UnitaryAdditiveCharacter.ofComplex ψ hc hne hu`. Its complex projection is
definitionally `ψ`, so the published
`Whittaker.mem_glFunctionals_iff_entrywise` converts each of the target's
entrywise covariance equations into membership in the existing
`Whittaker.glFunctionals` submodule.

For the first clause, the two functionals become subtype elements `L₁` and
`L₂`. The published theorem `Whittaker.multiplicityOne` applies with the
original admissibility and irreducibility hypotheses and the original
nonvanishing of the first underlying functional. It gives a unique complex
scalar with `L₂ = c • L₁`. Applying subtype projection gives the target's
equality of raw linear maps. Conversely, any competing raw scalar equality
lifts by subtype extensionality, so the bundled uniqueness proves raw
uniqueness as well. This includes a zero second functional.

For the second clause, `Whittaker.raw_exists_inverse_iff` gives exactly the
equivalence of nonzero-functional existence for `ψ` and `ψ⁻¹` on the same
representation. Its implemented proof uses the existing character-change
linear equivalence at `-1`, with injectivity preserving nonvanishing in both
directions.

For the third clause, the original irreducibility hypothesis is installed as
an instance and `Whittaker.raw_coefficient_injective` applies to each
specified nonzero equivariant functional. Its implemented proof uses the
published Whittaker model equivalence and subtype extensionality to deduce
injectivity of the actual map `v ↦ (g ↦ ℓ (ρ g v))`.

Rank one is included by all three imported interfaces. The proof asserts no
existence of a nonzero functional for every irreducible representation and
adds no topology or finite-dimensionality assumption on the carrier.

This module is an internal assembly of the published
[PrerequisiteInterfaces](PrerequisiteInterfaces.md) and
[MultiplicityOneProof](MultiplicityOneProof.md) modules. The
[unchanged statement](PrerequisitesStatement.md) records the original JPSS
source and the scalar, character-inversion and model formulations. The
multiplicity proof's companion documents its distribution and smooth-dual
route and source provenance. The assembly introduces no new literature
transcription or mathematical premise.
