# Continuous quotient lift (M014.002)

Worker 193 adapts Naganori Yamaguchi’s `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean>),
lines 37–50 (including its docstring). The full original file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Source correspondence

| Original declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.continuousQuotientLift` | `Langlands.NYLL.PortInternal.M014.d002` |

The definition takes independent implicit carriers `{A : Type uA}` and
`{B : Type uB}`, followed in source order by `[Group A]`,
`[TopologicalSpace A]`, `[Group B]`, `[TopologicalSpace B]`,
explicit `(N : Subgroup A)`, instance `[N.Normal]`, explicit
`(f : A →ₜ* B)` and explicit `(hN : N ≤ f.toMonoidHom.ker)`.
It returns `A ⧸ N →ₜ* B`, with the actual quotient topology.
No topological-group or separation assumption is added. The unused
ambient source variable `G` and its instances are not declaration parameters.

The construction is the original one: let `φ` be
`QuotientGroup.lift N f.toMonoidHom hN`, prove continuity after composition
with `QuotientGroup.mk' N` using `QuotientGroup.lift_mk'` and
`f.continuous_toFun`, then descend continuity through
`QuotientGroup.isQuotientMap_mk`. Both the algebraic homomorphism and
the proof terms inside the data definition are retained.

## Modifications and reuse

The source-private helper is exposed under the exact
`Langlands.NYLL.PortInternal.M014.d002` name required by Task 5824,
so downstream port units can import it. The local source namespace is
replaced accordingly; the `private` modifier is removed.
The source `noncomputable section` is retained. Extraction omits the unused
`CyclicCohomology` namespace opening, the unused ambient group section
variables and all other source declarations. No construction field, proof
body, parameter order or binder kind is changed. The three broad source
imports (`Degree.FrobeniusLift`, `ProfiniteIntegers.TopologicalGeneration`
and `Topology.TotallyDisconnectedQuotients`) are replaced by:

- `Mathlib.GroupTheory.QuotientGroup.Basic`
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`
- `Mathlib.Topology.Algebra.Group.Quotient`

The published dependencies and Mathlib constructions are reused by Lean name;
this unit introduces no instances. Exact-name Library search found no
previously published declaration for this source unit. The focused Mathlib
continuous-homomorphism, quotient and subgroup source search found no
bundled definition replacing this full source construction and telescope.

This is a data-definition candidate, including its intrinsic structure
proofs. It publishes no separate theorem target and claims no Frobenius
fixed-field, host class-formation, cohomology or reciprocity theorem.

## License

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already published in the Library and unchanged.
All modifications above are by Worker 193.
