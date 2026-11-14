# Nonarchimedean depth and quotient fibres

This module adapts three constructions from Naganori Yamaguchi's
`Nyll/ValuedFieldTheory/Ramification/Herbrand/Tower.lean` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The Lean module is
`Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Tower.Definitions`.
The declaration namespace is
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory`.

## Depth structure

`Langlands.NYLL.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory.NonarchimedeanDepth`
has exactly the parameters `(G : Type u) [Group G]` for a single arbitrary
universe `u`. Its data field is `depth : G → WithTop ℕ`, and its four
intrinsic laws are:

| Field | Exact law |
| --- | --- |
| `depth_eq_top_iff` | `∀ σ, depth σ = ⊤ ↔ σ = 1` |
| `depth_mul_ge_min` | `∀ σ τ, min (depth σ) (depth τ) ≤ depth (σ * τ)` |
| `depth_mul_eq_min_of_ne` | `∀ {σ τ}, depth σ ≠ depth τ → depth (σ * τ) = min (depth σ) (depth τ)` |
| `depth_conj` | `∀ γ σ, depth (γ * σ * γ⁻¹) = depth σ` |

Thus the identity has infinite depth, every other element has finite natural
depth, multiplication has the nonarchimedean lower bound, unequal factor
depths determine the product depth, and depth is invariant under conjugation.
These laws belong to the structure itself, exactly as in the source.

## Actual quotient fibre

In the nested namespace `NonarchimedeanDepth`, the complete argument list of
`QuotientFiber` is

```lean
{G : Type u} [Group G] (H : Subgroup G) [H.Normal] (q : G ⧸ H)
```

Its result is the actual subtype in the source:

```lean
{σ : G // QuotientGroup.mk' H σ = q}
```

The canonical quotient homomorphism is Mathlib's `QuotientGroup.mk' H`.
Normality supplies the group structure on the quotient and this homomorphism.
The subtype lives in `Type u`. Although the abbreviation is inside the depth
structure's namespace, its arguments contain no depth structure `D`.

## Coset equivalence and its inverse

`NonarchimedeanDepth.rightCosetEquivQuotientFiber` has the complete argument
list

```lean
{G : Type u} [Group G] (H : Subgroup G) [H.Normal] (σ : G)
```

and returns the actual equivalence

```lean
H ≃ QuotientFiber H (QuotientGroup.mk' H σ)
```

Its forward map sends `τ : H` to the element with underlying value
`σ * (τ : G)`. Its inverse sends an element `γ` of the specified fibre to the
element of `H` with underlying value `σ⁻¹ * (γ : G)`. Both formulas hold
definitionally in this implementation. The source's name is retained; the
underlying set is `σH`, which Mathlib calls a left coset, parametrized here by
multiplication of `σ` on the right by elements of `H`.

The implementation reuses Mathlib's `MonoidHom.fiberEquivKer` at
`f := QuotientGroup.mk' H` and the chosen representative `σ`. This existing
equivalence identifies `f ⁻¹' {f σ}` with `f.ker`, using `σ⁻¹ * γ` in the
forward direction and `σ * τ` in the inverse direction.
`Equiv.subtypeEquivRight`, with `QuotientGroup.eq_one_iff`, identifies `H`
with `f.ker` without changing underlying elements. Composing that
identification with `(f.fiberEquivKer σ).symm` gives the required orientation.
The preimage-of-singleton subtype is definitionally the stated `QuotientFiber`.

Both inverse-law certificates are fields of the constructed `Equiv`, inherited
through `Equiv.subtypeEquivRight`, `Equiv.symm` and `Equiv.trans`.
On underlying group elements they assert
`σ⁻¹ * (σ * τ) = τ` and `σ * (σ⁻¹ * γ) = γ`; subtype extensionality gives
the corresponding equalities in `H` and the fibre. The construction includes
the inverse and its certificates, without assuming a bijection as extra data.

All three declarations apply to arbitrary groups. There is no `Finite G`
assumption, no depth argument on either quotient declaration, and no introduced
`Fintype` instance. This definition unit does not state maximal-depth,
quotient-depth or finite-sum results.

## Pinned source correspondence and modifications

The pinned source is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/Herbrand/Tower.lean`.
Its SHA-256 is
`763a777c2d023162864577df54fa13cd643ee8e91c074e1465587d34e9e089a3`.
The source registration is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

In the table, `P` denotes
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory`.

| Original declaration | Pinned lines | Adapted declaration |
| --- | --- | --- |
| `NonarchimedeanDepth` | 44–55 | `P.NonarchimedeanDepth` |
| `NonarchimedeanDepth.QuotientFiber` | 73–74 | `P.NonarchimedeanDepth.QuotientFiber` |
| `NonarchimedeanDepth.rightCosetEquivQuotientFiber` | 141–150 | `P.NonarchimedeanDepth.rightCosetEquivQuotientFiber` |

Worker 542 added the `Langlands.NYLL` prefix, isolated the three source units,
and replaced the broad ramification import with
`Mathlib.GroupTheory.Coset.Basic`,
`Mathlib.GroupTheory.QuotientGroup.Defs`, and `Mathlib.Order.WithBot`.
The structure's fields and the fibre's body are unchanged. The equivalence's
original explicit constructor proofs were replaced by the existing Mathlib
equivalence and predicate identification described above, preserving both maps
and their inverses. The unused surrounding depth variable and the source's
`noncomputable section` are unnecessary for these declarations. The four local
finite-type instances at source lines 76–87 are omitted. The recorded NYLL
compatibility patch10 does not modify this source module, and none of its
patches is used here.

Library and TaskHub searches found no matching depth structure or these
named quotient interfaces. The generic fibre equivalence in Mathlib supplies
the construction used here. No relevant NYLL or Herbrand erratum was found in
the published errata lookup.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean
4.34.0 with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The Mathlib construction is in `Mathlib/GroupTheory/Coset/Basic.lean`,
lines 471–488; the quotient membership characterization is in
`Mathlib/GroupTheory/QuotientGroup/Defs.lean`.

## Attribution

The original Lean copyright and author header is retained: copyright 2026
Naganori Yamaguchi, author Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing upstream
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Their SHA-256 hashes are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The upstream supplementary attribution registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
