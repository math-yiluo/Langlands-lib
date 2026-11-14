# Full decomposition group over the fixed field of a closed subgroup: target

This module states NYLL source unit M250.005 as a closed proposition. It
exports one Prop-valued `def` in namespace
`Langlands.NYLL.LocalClassFieldTheory`:

- `localAbstractFixedDecompositionGroup_eq_topStatement` (M250.005).

Nothing is proved here. The proof is a separate unit under the adapted source
name `Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top`.

Mathematically, let `K` be a nonarchimedean local field, let `K^sep` be its
separable closure and let `B` be the valuation ring
`localSeparableValuationSubring K` of `K^sep` chosen in M249.006. Let `H` be
a closed subgroup of `Gal(K^sep/K)` and let `E = (K^sep)^H` be its fixed
field. The statement says that every automorphism `τ` of `K^sep` over `E`
satisfies `τ • B = B`. In other words, the decomposition group of `B` over
`E` is all of `Gal(K^sep/E)`.

The source docstring calls this the base-change form of the full
decomposition-group statement proved for `K` (M249.010: every automorphism
of `K^sep` over `K` preserves `B`).

## The proposition

```lean
def localAbstractFixedDecompositionGroup_eq_topStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))),
    decompositionGroup (abstractFixedField K (SeparableClosure K) H)
      (localSeparableValuationSubring K) = ⊤
```

There is no level parameter: `K` lives in `Type`, as in the source. The
quantified binders, in order, are the section variables of the source (lines
33–34) followed by the theorem's own explicit binder `H`.

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| `H : ClosedSubgroup (Gal(SeparableClosure K/K))` | a closed subgroup of the Galois group of `SeparableClosure K` over `K` (Mathlib's `ClosedSubgroup` with the Krull topology) |

The field `abstractFixedField K (SeparableClosure K) H` is an
`IntermediateField K (SeparableClosure K)`. Its Mathlib coercion to a type
carries a field structure and an algebra structure on `SeparableClosure K`,
and `decompositionGroup` uses these. So the left-hand side is a subgroup of
`SeparableClosure K ≃ₐ[E] SeparableClosure K`, and `⊤` is the whole group.

### Published declarations used

- `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup`
  (M239.001,
  [definition](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring/Definitions.md)):
  for a field extension `L/F` and a valuation subring `A` of `L`,
  `decompositionGroup F A` abbreviates Mathlib's `A.decompositionSubgroup F`,
  the subgroup of `L ≃ₐ[F] L` of automorphisms `σ` with `σ • A = A`. Here
  `F = E` and `L = SeparableClosure K`.
- `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`
  (M099.001,
  [definition](../../FiniteAbstractFixedField/Initial/Definitions.md)):
  `abstractFixedField K (SeparableClosure K) H` is the abbreviation
  `IntermediateField.fixedField H.toSubgroup`, the subfield of
  `SeparableClosure K` fixed by `H`.
- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../../LocalResidueDatum/U006/Definitions.md)): the
  valuation ring `B` of `SeparableClosure K`, the preimage of a valuation
  subring of `AlgebraicClosure K` chosen by Chevalley's extension theorem.

`ClosedSubgroup`, `Gal(_/_)`, `SeparableClosure` and `IntermediateField` are
Mathlib declarations.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `1fbff4b8a0dd4bcb09d8ea295cc0c6a1a35802af`, compiled the module with no
errors or warnings (diagnostic `6217a74c-14b9-4c6f-9086-aa6a65a5838d`).

The same check compiled a private probe against this module. The probe
proved the target by the source proof after `intro K _ _ _ _ H`. That proof
restricts the scalars of `τ` to `K` and applies the published theorem
`localSeparableDecompositionGroup_eq_top` (M249.010). This shows that the
target is the intended proposition. The proof is not part of this module.

## Imports and scope

The imports are the published modules
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`
(for `localSeparableValuationSubring`),
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`
(for `abstractFixedField`) and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`
(for `decompositionGroup`).

Only M250.005 is stated. The earlier unit M250.001 is published as a
[definition](../U001/Definitions.md). The local instances M250.002–M250.004
and the later units of the source file are not part of this module.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean#L80-L97)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `84865498b7b4788c2ebeecb92aeaca7a1bb9a62e2005cb1554386e2a52bf674a`, the
value recorded for M250 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m250).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M250.005 | theorem `localAbstractFixedDecompositionGroup_eq_top` | 80–86 (proof 86–97) | `localAbstractFixedDecompositionGroup_eq_topStatement` |

Lines 80–82 are the doc comment, line 83 the theorem name, and lines 84–86
its binder and type; the proof occupies lines 86–97. The source module opens
namespace `LocalClassFieldTheory` (line 20), opens `CyclicCohomology`,
`RamificationTheory` and `ClassFormation` (line 21), `LocalFieldTheory`
(line 23), `scoped Pointwise ValuativeRel` (line 29),
`HilbertRamification.ValuationSubring` (line 30) and
`Field.absoluteGaloisGroup` (line 31), works in `noncomputable section`
(line 27) and declares the section variables at lines 33–34.

Worker 85 made these changes on 14 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and to the opened
  namespace, which becomes
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`;
- packaged the theorem type as a closed proposition, a `def` with the suffix
  `Statement`. The section variables become the leading `∀`-binders, with the
  same kinds (explicit for `K`, instance-implicit for the rest), followed by
  the explicit binder `H`. The type after the binders is the source type
  unchanged. The doc comment is the source doc comment;
- omitted the proof, the `noncomputable section`, the other `open` lines and
  all other declarations;
- replaced the source imports by the published modules above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
