# Finite-dimensionality in the relative fixed-field presentation

`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional`
proves exactly the published
`abstractRelativeFixedField_finiteDimensionalStatement k Ω K L hLK hKfinite hLKfinite`.
It keeps the source's Type-0 fields, field/algebra/Galois instances, closed
subgroups `L ≤ K`, and both finite-quotient hypotheses. The conclusion uses
the actual `abstractRelativeFixedField` with its published scalar structure.

## Implemented proof and dependencies

The private lemma `relativeFiniteDimensional_local` implements M099.018.
It installs the inclusion algebra, its scalar tower with `k`, and the two
finite-quotient witnesses. The published
`ClassFormation.FiniteGaloisSubextension.finite_extension_trans` (M040.024)
gives the absolute finite quotient for `L`; the published
`abstractFixedField_finiteDimensional` (M099.005) gives finite-dimensionality
over `k`; Mathlib's `FiniteDimensional.right` gives relative
finite-dimensionality of the ordinary upper fixed field. The inclusion uses
the published `abstractFixedField_le` (M099.006).

The public theorem installs that inclusion algebra and the private lemma's
finite-dimensional instance. It constructs an identity-carrier linear
equivalence from `abstractFixedField k Ω L` to
`abstractRelativeFixedField k Ω hLK`: both directions retain the ambient value
and membership witness, and all inverse, addition and scalar identities are
reflexive. `LinearEquiv.finiteDimensional` transports the finite-dimensional
instance to the relative presentation.

M099.018 is included only under a private, distinct name because its separately
submitted proof is not yet published. This is permitted by the task and makes
this candidate independent of that pending publication. No second public copy
of the adapted M099.018 name is introduced. Other dependencies are the four
focused published imports and Mathlib. All added instances are local, and the
statement and its imported files remain unchanged.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
M099.019 has signature lines 339–347 and proof lines 348–363; the private
M099.018 copy has signature lines 306–317 and proof lines 318–335. The file
SHA-256 is `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The port isolates M099.019 and its private prerequisite, prefixes the namespace
with `Langlands.NYLL`, replaces source imports by focused published modules,
states the exact published `Statement` application, and replaces the source
M099.018 call by its private name. The source proof bodies are otherwise
unchanged. Unused namespace openings and unrelated declarations are omitted.
This proves only the specified NYLL support result.

The original copyright, authorship and Apache-2.0 header are retained.
The original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
