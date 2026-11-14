# Extension embedding from reverse norm inclusion: proposition target

This module defines the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.nonempty_algHom_of_normSubgroup_leStatement`.
Inside `namespace Langlands.NYLL.LocalClassFieldTheory`, with
`open LocalFieldTheory`, its complete body is

```lean
∀ (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  [IsAbelianGalois K L] [IsAbelianGalois K M]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (h : localNormSubgroup K M ≤ localNormSubgroup K L),
  Nonempty (L →ₐ[K] M)
```

For finite abelian Galois extensions `L/K` and `M/K` of the same
nonarchimedean local field, reverse inclusion
`N_{M/K}(Mˣ) ≤ N_{L/K}(Lˣ)` is asserted to imply the existence of a
`K`-algebra homomorphism `L → M`. Such a homomorphism between fields is
injective. The module defines this proposition; it supplies no proof.

All three fields are in `Type`, that is universe zero, exactly as in the
source. There are no universe parameters or hidden section parameters.
The explicit field parameters, instance binders and their order, and the
explicit hypothesis `h` are retained. Only `K` has valuation and topology
instances in the telescope. There is no `Algebra L M` premise, supplied
embedding, abstract order-reversal assumption, or chosen separable closure.

The norm subgroup is the existing
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`, the range of
`Langlands.NYLL.LocalFieldTheory.normUnits K L = Units.map (Algebra.norm K)`.
It is a subgroup of the actual unit group `Kˣ`, and the inclusion uses this
same construction for `M`. The classes `Field`, `Algebra`,
`FiniteDimensional`, `IsAbelianGalois`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`, and the algebra
homomorphism type in the conclusion, are the existing Mathlib objects.

## Source and changes

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean#L83-L127).
Unit M402.003 is the theorem at lines 85–127; its signature is lines
85–93, its docstring is lines 83–84, and its proof is lines 94–127.
The complete source file was read, including the enclosing
`noncomputable section`, namespace and openings at lines 26–31.
It declares no preceding `universe` or `variable` commands.
The file's SHA-256 is
`173d65750c2a18cc233fcc94d9fde94e88c7a42709cfb9c27e50bae8e971ba06`.
The published [M402 inventory](../../../../../../../../notes/reuse/nyll-public-port/m385-m408.md#m402)
identifies the same unit and pin.

| Source | Adapted |
| --- | --- |
| theorem `LocalClassFieldTheory.nonempty_algHom_of_normSubgroup_le` | Prop definition `Langlands.NYLL.LocalClassFieldTheory.nonempty_algHom_of_normSubgroup_leStatement` |
| `LocalFieldTheory.localNormSubgroup` | published `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `IsAbelianGalois`, `IsNonarchimedeanLocalField` and the other Mathlib objects | the same Mathlib declarations |

Worker 547 made the following modifications on 14 November 2026:
the namespace receives the `Langlands.NYLL` prefix; the theorem name
receives `Statement`; the complete theorem telescope is universally closed
as a `def ... : Prop`; and the source proof is omitted. The original
docstring is preserved. The source's unused namespace openings for
`RamificationTheory`, `CyclicCohomology`, `KummerTheory` and
`ClassFormation`, and its unnecessary `noncomputable section`, are omitted.
No instance is declared, and no local or scoped instance is promoted.
The unused-variable linter is disabled locally for this definition so
that the source's explicit hypothesis name `h` is retained without a warning.
There are no other changes to the source hypotheses, binder kinds,
universes, objects or conclusion.

The source imports are replaced by the published
`NormQuotient.U001.Definitions` module and
`Mathlib.FieldTheory.Galois.Abelian` and
`Mathlib.NumberTheory.LocalField.Basic`. The norm-subgroup Lean/Markdown
pair and these two Mathlib class definitions were read before reuse.
The reduced imports suffice for the target's type. The conservative
M402.001/M402.002/M298.029 scheduling dependencies concern the later proof:
the source proof realizes both extensions in the separable closure,
transports the norm inclusion using M402.002, invokes the abstract
`FiniteAbelianSubextension.le_iff_normSubgroup_le` (M298.029), and uses the
Galois correspondence to obtain the embedding. None of these results is
added as a premise or claimed as proved here.

The retained snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the Library's `notes/errata`.

The original Apache-2.0 copyright and author header is retained verbatim.
The Library's [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. No other worker's draft or implementation was reused.

## Development checks

Lean-service check `eedbc246-d705-4c3d-a067-438481deed1f` compiled the
entry module with no errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Declaration inspection
reported `kind: definition`, `statement_returns_prop: true` and no
universe parameters.

Private diagnostic check `84a87874-5abe-4cd6-888f-3b2fc8f277f0`
printed the complete definition with full names and universes and
verified by reflexivity its equality to the displayed telescope with
fully qualified norm-subgroup and Mathlib class names. It succeeded;
its sole warning concerned the retained hypothesis name `h` in that
private comparison. The diagnostic is outside the contribution.
These development checks establish neither a proof of the proposition
nor independent semantic acceptance.
