# Projection to unramified norm classes

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass` is:

The canonical quotient homomorphism `Kˣ →* Kˣ ⧸ unramifiedNormSubgroup K n`, defined as `QuotientGroup.mk' (unramifiedNormSubgroup K n)`. The subgroup is the published valuation-divisibility subgroup on the actual field units.

The explicit field parameter is `K : Type u` for arbitrary universe `u`.
The instance parameters, in source order, are `[Field K] [ValuativeRel K]`
`[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, followed by an
explicit `n : Nat`. Zero degree remains allowed; no positivity or nonzero
condition is added. The normalized valuation convention is unchanged.

No preceding membership theorem is needed for this projection: Mathlib supplies the quotient map for the published subgroup. The ambient unit group is commutative, so its subgroup is normal by existing Mathlib instances; this module adds no instance.

## Source and changes

This is M266.013, `LocalClassFieldTheory.unramifiedNormClass`, lines 150–154
of `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The full source file was read;
its SHA-256 is `ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by that path.
No applicable entry was found in the project errata notes.

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.unramifiedNormClass` | `Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass` |

Worker 205 extracted this one definition, prefixed its namespace with
`Langlands.NYLL`, and replaced the source imports by:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U011.Definitions`.
- `Mathlib.GroupTheory.QuotientGroup.Defs`.

The universe, parameter telescope, result type, construction body, and
noncomputable section are unchanged. The focused imports use the existing
published NYLL data by Lean name; they introduce no duplicate valuation,
subgroup or Artin map. This unit claims only the definition, with its
properties reserved for separate proposition targets and proofs.

The original copyright and author header is retained. The Apache-2.0 license
and notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or other worker's draft was reused.

The focused Lean-service check succeeded with zero errors and warnings in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`. Declaration inspection
confirmed universe `u` and only `propext`, `Classical.choice`, and `Quot.sound`.
This verifies that the smaller import set suffices without the preceding M266
property proofs or the source Norm and NormQuotient imports.
