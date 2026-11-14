# The normal-basis span equals the chosen integer lattice

`Langlands.NYLL.LocalClassFieldTheory.span_normalBasis_eq_chosenNormalBasisIntegerLattice`
proves the exact published proposition with suffix `Statement`. For a finite
Galois extension `L/K` and a valuative relation on `K`, the integer-ring span of
Mathlib's normal-basis vectors is the chosen normal-basis integer lattice. The
source telescope retains fields `K L : Type u`, with `[Field K] [ValuativeRel K]
[Field L]`, the algebra, finite-dimensional and Galois instances in that order.

The proof unfolds the published proposition and the lattice's defining span.
It reduces to equality of the two generating ranges. In each direction the same
Galois automorphism indexes the witness; Mathlib's `IsGalois.normalBasis_apply`
identifies that vector with its action on the vector indexed by the identity.
Congruence of `Submodule.span` finishes the equality. This is the source proof
with the definitional equality M144.003 unfolded directly, so there is no
unpublished sibling-proof dependency or duplicate theorem under its reserved
name. The only import is the published `NormalBasis.SpanStatement` module,
which already imports the lattice definition and Mathlib's normal-basis API.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 32–44, M152.001. The unfolded definitional equality is
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 59–64,
M144.003. Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Worker 517 extracted the unit, prefixed its namespace with `Langlands.NYLL`,
reduced imports, used the published proposition and made the unfolding
adaptation above. The original author/copyright header is retained;
Apache-2.0 LICENSE and NOTICE remain in `licenses/NYLL/`.
