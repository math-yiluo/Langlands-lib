# Principal-unit membership and the zeroth subgroup

This module introduces exactly two closed proposition definitions in
`Langlands.NYLL.LocalFieldTheory`. For a field `K : Type u` with the supplied
`ValuativeRel K`, write

```lean
O = Valuation.integer (ValuativeRel.valuation K)
m = IsLocalRing.maximalIdeal O
```

These denote Mathlib's actual valuation integer ring and its canonical maximal
ideal. The scope `ValuativeRel` writes them as `𝒪[K]` and `𝓂[K]`. The subgroup
`principalUnits K n` is the published
`Langlands.NYLL.LocalFieldTheory.principalUnits`, with ambient group `Oˣ`.

With `open scoped ValuativeRel`, the complete definitions are:

```lean
def MemPrincipalUnitsIffStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] (a : 𝒪[K]ˣ) (n : Nat),
    a ∈ principalUnits K n ↔ ((a : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

def PrincipalUnitsZeroStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K],
    principalUnits K 0 = (⊤ : Subgroup 𝒪[K]ˣ)
```

Here `.{u}` displays each declaration's single arbitrary universe parameter.
Each unapplied declaration has type `Prop`; the field, both typeclass instances,
and the membership target's unit and natural index are quantified inside its
body. The membership proposition asserts the direct iff for every natural
index, including zero. The zero-step proposition asserts equality in the
subgroup lattice of valuation-ring units.

The only hypotheses are `Field K` and `ValuativeRel K`. The targets require no
topology, discreteness, nonarchimedean-local-field structure, finite residue
field, completeness, characteristic restriction, or nontrivial valuation.
No conclusion is assumed as input, and no certificate parameter is introduced.
This module states the two propositions; it exports no proof theorem.

## Source correspondence and proof provenance

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L19-L76).
Its SHA-256 is
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.
The source's lines 19–76 were read in full for this unit.

| Partition unit and source declaration | Source lines | Closed target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- |
| M131.002, `LocalFieldTheory.mem_principalUnits_iff` | 54–57 | `MemPrincipalUnitsIffStatement` |
| M131.004, `LocalFieldTheory.principalUnits_zero` | 73–76 | `PrincipalUnitsZeroStatement` |

The source membership proof is `Iff.rfl`, since the subgroup's carrier is the
displayed ideal-membership condition. The source zero-step proof is `ext u`
followed by `simp [principalUnits]`: after extensionality, the zeroth ideal
power simplifies to the top ideal. These descriptions record the original
proof routes for later exact-target proof tasks. Neither proof is supplied
by this statement module.

M131.003, `principalUnits_integerRingEquiv_mem`, is an intervening independent
automorphism theorem. It supplies no definition needed by either target. The
partition's conservative M131.003.END scheduling edge for M131.004 is not a
mathematical dependency of these targets. Automorphism, antitonicity, quotient,
inertia and reciprocity statements remain outside this unit.

## Adaptation, imports and attribution

Worker 587 adapted the two source theorem conclusions by prefixing the
namespace with `Langlands.NYLL`, naming the closed targets as above, and moving
all mathematical parameters and instances inside their `Prop` bodies. The
membership unit binder is renamed from `u` to `a`. The zero-step top subgroup's
type is explicit. The theorem proofs and the zero theorem's `simp` attribute
are omitted. The source's broad module documentation is replaced with the
scope of these two targets.

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`.
That published definition imports
`Mathlib.Topology.Algebra.Valued.ValuativeRel`,
`Mathlib.RingTheory.Ideal.Operations`, and `Mathlib.Tactic.Ring`.
It supplies the subgroup and canonical ring/ideal structures used here.
The original broad `Basic` and `PrincipalUnits` module closures are not ported.
No host p-adic field filtration, field-unit subgroup, or replacement
valuation-ring structure is introduced.

The registered original is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata file was present in the supplied project notes or the
pinned published Library notes. The original copyright and author header is
preserved. The unchanged upstream Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library,
with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected file is not listed in the root NOTICE's third-party source table.
No additional third-party implementation or modified worker draft is copied.
Worker 106 supplied task routing, rather than an implementation contribution.

## Development inspection

The project Lean service successfully built this module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Exact unapplied-declaration checks
`0ee28f5d-a87b-404b-90cd-626552209d3f` and
`1d73a471-e763-4c12-9e63-9448d420ed5c` each returned `ok: true`,
`statement_returns_prop: true`, level parameters `[u]`, and zero errors or
warnings. A private diagnostic module printed both complete bodies with
universe levels in successful check `34b7e9ed-4d54-4a6e-98f9-035cc8dea705`,
confirming the internal quantifiers and canonical integer-ring/maximal-ideal
constructions. These development checks establish compilation and inspection;
independent semantic acceptance and publication remain separate.
