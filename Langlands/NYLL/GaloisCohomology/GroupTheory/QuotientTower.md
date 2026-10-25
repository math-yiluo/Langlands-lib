# Quotient types in subgroup towers

This module adapts the two definitions in Naganori Yamaguchi's
`Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean`, lines 30–60, at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. It imports only
`Mathlib.GroupTheory.Index` and preserves the arbitrary universe `u` and the
assumption `{G : Type u} [Group G]`.

## Quotient convention and scope

For a subgroup `S` of a group `A`, the notation `A ⧸ S` denotes the type of left
cosets. Its equivalence relation is `x ~ y` if and only if `x⁻¹ * y ∈ S`, as in
`QuotientGroup.leftRel_apply`. This construction does not require `S` to be
normal. Both declarations below return `Equiv` objects (`≃`) between types;
they assert neither group isomorphisms nor cardinal-index formulas. They apply
to infinite groups and subgroups without any finiteness assumption.

`M.subgroupOf H` means the inverse image of `M` under the subtype homomorphism
`H →* G`. As a subgroup of `H`, it consists of the elements lying in `M`; this
notation is meaningful even when `M` is not contained in `H`.

## Flattening a nested subgroup quotient

`Langlands.NYLL.Subgroup.quotientSubgroupOfEquiv` has implicit subgroups
`{H K M : Subgroup G}` and the sole explicit hypothesis `(hHK : H ≤ K)`. Its
result is

```lean
(↑(H.subgroupOf K) ⧸ (M.subgroupOf K).subgroupOf (H.subgroupOf K)) ≃
  (↑H ⧸ M.subgroupOf H)
```

There is no assumption `M ≤ H` or `M ≤ K`. Mathlib's
`Subgroup.subgroupOfEquivOfLe hHK` removes the extra subtype layer from an
element of `H.subgroupOf K`; its inverse restores that layer using `hHK`.
The implementation lifts both functions to the quotient using `Quotient.map'`.
After rewriting with `QuotientGroup.leftRel_apply`, preservation of the
relation in either direction is the same membership fact in `M`, definitionally.

For each inverse law, quotient induction reduces to a representative. The
calculation of `Quotient.map'` on that representative and the corresponding
inverse law of `subgroupOfEquivOfLe` prove the quotient equality via
`congrArg Quotient.mk''`. Thus both inverse certificates are constructed,
without an additional hypothesis or an unproved equivalence.

## Decomposing a subgroup tower

`Langlands.NYLL.Subgroup.quotientTowerEquiv` has implicit subgroups
`{M L K : Subgroup G}` and explicit hypotheses `(hML : M ≤ L) (hLK : L ≤ K)`.
Its result is

```lean
(K ⧸ M.subgroupOf K) ≃
  (K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L)
```

First, `Subgroup.subgroupOf_mono K hML` gives the inclusion of the two
subgroups inside `K`. Mathlib's `Subgroup.quotientEquivProdOfLE` then identifies
the left side with

```lean
(K ⧸ L.subgroupOf K) ×
  (↑(L.subgroupOf K) ⧸ (M.subgroupOf K).subgroupOf (L.subgroupOf K))
```

The implementation composes this equivalence with `Equiv.prodCongr`, leaving
the first factor fixed and applying `quotientSubgroupOfEquiv hLK` to the second.
All inverse certificates are inherited from these equivalences. The tower
construction is noncomputable: Mathlib's product decomposition uses
`Quotient.out` to choose a representative of each coset of `L.subgroupOf K`.
Its first coordinate is the coarser coset; its second coordinate records the
remaining factor in `L` relative to the chosen representative. No canonical
choice of this second coordinate is asserted.

## Source correspondence and modifications

The original file was read in full. Its SHA-256 is
`41d0b248e0b5cec84e6e20e7185a18746b8f79e2e9ba203ef7713c7c00a89115`.
It is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean`.

| Original declaration and lines | Adapted declaration |
| --- | --- |
| `Subgroup.quotientSubgroupOfEquiv`, 30–52 | `Langlands.NYLL.Subgroup.quotientSubgroupOfEquiv` |
| `Subgroup.quotientTowerEquiv`, 56–60 | `Langlands.NYLL.Subgroup.quotientTowerEquiv` |

Worker 22 changed the enclosing namespace, explicitly qualified the three
Mathlib subgroup construction names, and revised module documentation to state
the scope of this adaptation. The definition bodies and inverse-law arguments
otherwise follow the original. The previously recorded NYLL compatibility
patch10 makes no change to this source file; none of its patches is used here.
No applicable erratum was found in the project and Library notes lookup.

The source registration is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the precise locator is the source path above, lines 30–60. Supplementary
attribution files are registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright and author header is retained in the Lean file:
Naganori Yamaguchi, 2026, assisted by OpenAI Codex, Apache-2.0.
The original [LICENSE](../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../licenses/NYLL/NOTICE) are copied
unchanged under `Langlands/NYLL/`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither the original NOTICE nor the supplement's third-party attribution
records names this selected source file; no third-party source module is copied.

The pinned Mathlib implementations reused here are `subgroupOf`,
`subgroupOfEquivOfLe`, and `subgroupOf_mono` in
`Mathlib/Algebra/Group/Subgroup/Map.lean`, and `quotientEquivProdOfLE` in
`Mathlib/GroupTheory/Coset/Basic.lean`. Existing Library uses of subgroup
reindexing and coset products do not supply these exact general quotient
interfaces. The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
