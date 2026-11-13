# Continuous subgroup inclusion (M014.003)

Worker 193 adapts Naganori Yamaguchi’s `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean>),
lines 52–57 (including its docstring). The full original file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Source correspondence

| Original declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.continuousSubgroupSubtype` | `Langlands.NYLL.PortInternal.M014.d003` |

The implicit carrier `{A : Type uA}` is universe-polymorphic, followed
in source order by `[Group A]`, `[TopologicalSpace A]` and explicit
`(H : Subgroup A)`. The result is `H →ₜ* A` using the actual subgroup
and its subtype topology. The unused ambient `G` is not a declaration
parameter, and no `IsTopologicalGroup A` hypothesis is added.

The adapted body reuses the published
`Langlands.Continuous.subgroupInclusion H`, from
`Langlands/Cohomology/Continuous/FiniteQuotientSystem.lean`.
That definition has exactly the source telescope above. Its fields are
`toMonoidHom := H.subtype` and
`continuous_toFun := continuous_subtype_val`, so unfolding it gives
the original source construction by definitional equality.

## Modifications and reuse

The source-private helper is exposed as a wrapper under the exact
`Langlands.NYLL.PortInternal.M014.d003` name required by Task 5824,
so downstream port units can import it. The local source namespace is
replaced accordingly; the `private` modifier is removed.
The source `noncomputable section` is retained. Extraction omits the unused
`CyclicCohomology` namespace opening, the unused ambient group section
variables and all other source declarations. Parameter order and binder kinds
are unchanged. The original structure literal is replaced by the exact Library
definition named above; its construction fields and intrinsic continuity proof
are definitionally equal to the original. The three broad source
imports (`Degree.FrobeniusLift`, `ProfiniteIntegers.TopologicalGeneration`
and `Topology.TotallyDisconnectedQuotients`) are replaced by the single import
`Langlands.Cohomology.Continuous.FiniteQuotientSystem`.

The published replacement and the wrapper both pass a focused check against the
complete source telescope, by direct unapplied-constant assignment:

```lean
universe uA
example : ∀ {A : Type uA} [Group A] [TopologicalSpace A]
    (H : Subgroup A), H →ₜ* A :=
  @Langlands.Continuous.subgroupInclusion

example : ∀ {A : Type uA} [Group A] [TopologicalSpace A]
    (H : Subgroup A), H →ₜ* A :=
  @Langlands.NYLL.PortInternal.M014.d003
```

The same focused check verifies by `rfl` that `d003 H` equals both
`Langlands.Continuous.subgroupInclusion H` and the original structure literal,
with the full carrier and instance parameters arbitrary. This discharges
M014.003 by exact Library reuse as allowed by required result 3 of Task 5824.
The unit introduces only the wrapper and no instances.

This is a data-definition candidate, including its intrinsic structure
proofs. It publishes no separate theorem target and claims no Frobenius
fixed-field, host class-formation, cohomology or reciprocity theorem.

## License

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already published in the Library and unchanged.
All modifications above are by Worker 193.
