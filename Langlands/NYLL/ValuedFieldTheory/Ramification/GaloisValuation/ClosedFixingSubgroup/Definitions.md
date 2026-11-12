# Closed fixing subgroups

This module adapts exactly M087.001 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup.lean#L23-L29),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The definition with its
documentation string and attribute is at lines 23–29; the imports are at
lines 7–8 and the enclosing `noncomputable section` and namespace at
lines 19–21 and 30. The original file is the whole of source module M087
and contains no other declaration. Its SHA-256 is
`5d07198f401853c274fe03415c1c85e243b2373d78f1dfb265f344dda5c3e4d7`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source
path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the project or Library errata
lookup. The public declaration partition identifies this file as M087,
family `R`, with no NYLL imports and no patch10 change.

## Interface and meaning

The complete interface, with namespace `Langlands.NYLL.RamificationTheory`
open, is:

```lean
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩
```

The base field `k`, the field `Ω` and the intermediate field `K` are
explicit, in this order. `Type*` gives `k` and `Ω` two independent,
arbitrary universe levels; the Lean service reports the level parameters
`u_1` and `u_2`. The instance arguments are the two field structures, the
algebra structure of `Ω` over `k`, and the hypothesis that `Ω/k` is
Galois. No finiteness, separability beyond `IsGalois`, characteristic or
valuation hypothesis is added.

The value is a closed subgroup of `Gal(Ω/k)`, the group `Ω ≃ₐ[k] Ω` of
`k`-algebra automorphisms of `Ω`. Mathlib's `ClosedSubgroup G` extends
`Subgroup G` by the field `isClosed'` stating that the carrier is closed.
The topology is Mathlib's instance `krullTopology k Ω`, the Krull
topology. Thus `closedFixingSubgroup k Ω K` is the subgroup of automorphisms
fixing every element of `K`, that is `Gal(Ω/K)` inside `Gal(Ω/k)`,
together with the certificate that it is Krull-closed.

The body reuses existing Mathlib declarations without restating them:

- `IntermediateField.fixingSubgroup K : Subgroup Gal(Ω/k)`
  (`Mathlib/FieldTheory/Galois/Basic.lean`) supplies the subgroup. It is
  Mathlib's `fixingSubgroup Gal(Ω/k) (K : Set Ω)`, the automorphisms
  fixing `K` pointwise.
- `InfiniteGalois.fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K]`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`) supplies the closedness of
  its carrier for every intermediate field of a Galois extension, finite
  or infinite.

The definition introduces no new subgroup, topology or closure argument.
Mathlib's order isomorphism
`InfiniteGalois.IntermediateFieldEquivClosedSubgroup` has the same
anonymous constructor `⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩` as
its forward map, but it lands in the order dual
`(ClosedSubgroup Gal(K/k))ᵒᵈ` and takes `k` and `K` implicitly. The source
consumers (for example in
`Nyll/ClassFieldTheory/AlgebraicFunctionFieldTheory/Fields/EmbeddedFixedFieldTower.lean`
and `Nyll/ClassFieldTheory/AlgebraicFunctionFieldTheory/Artin/NativePresentation.lean`)
apply the explicit three-argument name
`closedFixingSubgroup k Ω K` and use its `toSubgroup` projection, so the
named definition is retained rather than replaced by that order
isomorphism.

The attribute `@[implicit_reducible]` is kept. In the approved Lean
4.34.0, it lets the definition unfold when Lean checks implicit and
instance-implicit arguments for definitional equality, while keeping it
opaque to type class search. The definition is `noncomputable`, as in the
source, inside the source's `noncomputable section`.

## Exact declaration map and modifications

| Source declaration | Adapted declaration |
| --- | --- |
| `RamificationTheory.closedFixingSubgroup` (M087.001) | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` |

The only changes are these:

- The namespace `RamificationTheory` becomes
  `Langlands.NYLL.RamificationTheory`.
- The module moves from
  `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup.lean`
  to
  `Langlands/NYLL/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup/Definitions.lean`.
- The module documentation keeps the original first paragraph and adds
  the adaptation record.

The original imports `Mathlib.FieldTheory.Galois.Infinite` and
`Mathlib.FieldTheory.Galois.Profinite` are kept unchanged. A focused
build of this module alone, in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), compiled with no errors or
warnings, so these Mathlib-only imports suffice. The documentation string,
attribute, binders, universes, result type and body are unchanged. No
proof, placeholder proposition or global instance is added.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical
to the pinned originals. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The source file has no entry in the root NOTICE's third-party path
inventory.

Worker 5181 checked the original source and the Mathlib reuse
candidates, implemented this focused extraction and wrote this
documentation on 10 November 2026. The Lean header records the
modifications.
