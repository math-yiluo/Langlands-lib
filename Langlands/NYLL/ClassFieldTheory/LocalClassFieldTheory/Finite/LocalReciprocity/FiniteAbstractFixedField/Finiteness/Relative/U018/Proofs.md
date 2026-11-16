# Relative finite-dimensionality of abstract fixed fields

`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_relativeFiniteDimensional`
proves exactly the published
`abstractFixedField_relativeFiniteDimensionalStatement k Ω K L hLK hKfinite hLKfinite`.
For Type-0 fields `k`, `Ω` with `Algebra k Ω` and `IsGalois k Ω`, closed
subgroups `L ≤ K` and finite absolute and relative coset spaces, the upper
fixed field is finite-dimensional over the lower one through the inclusion
algebra specified by the target. All parameters and hypotheses are retained.

## Implemented proof

Install the inclusion algebra on the two fixed fields and its scalar tower
with `k`, using `IsScalarTower.of_algebraMap_eq' rfl`. Install both given
finite-quotient witnesses locally. The published
`ClassFormation.FiniteGaloisSubextension.finite_extension_trans` (M040.024)
gives finiteness of the absolute quotient for `L`. The published
`abstractFixedField_finiteDimensional` (M099.005) then makes its fixed field
finite-dimensional over `k`. Mathlib's `FiniteDimensional.right` gives the
relative finite-dimensionality over the fixed field of `K`.

The target supplies the exact algebra via `IntermediateField.inclusion`
and the published `abstractFixedField_le` (M099.006). All instances introduced
by the proof are local. The statement and its imported files are unchanged.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
M099.018, signature lines 306–317 and proof lines 318–335. The original file
has SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`
and is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The proof body follows the source unchanged. The port isolates this theorem,
prefixes its namespace with `Langlands.NYLL`, replaces the source imports by
the three focused published modules in this file, states the exact published
`Statement` application as the theorem type, and omits unused namespace
openings and unrelated source declarations. No private prerequisite proof is
needed. This proves only the stated NYLL support result.

The original copyright, authorship and Apache-2.0 header are retained.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for the retained license
and notices.
