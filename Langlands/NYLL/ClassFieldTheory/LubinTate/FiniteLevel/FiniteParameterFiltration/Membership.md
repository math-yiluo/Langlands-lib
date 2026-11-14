# Finite parameter subgroup membership proof (M363.002)

`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_mem_subgroup_iff`
proves the exact target
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_mem_subgroup_iffStatement`.
For a shared `LocalField.{u,v} K` package `F`, naturals `n k`, a proof
`hk : k ≤ n + 1` and a valuation-ring unit `u`, the canonical class of `u`
belongs to the finite level-`k` parameter subgroup exactly when `u`
belongs to the concrete higher-principal-unit group at `k`.
The source telescope, independent universes and explicit bound are retained.

## Implemented proof

A unit `a` lies in `higherPrincipalUnitGroup F.toCompleteDVF m` when
`a - 1` lies in the `m`-th power of the maximal ideal. Ideal-power
inclusion `Ideal.pow_le_pow_right hk` therefore proves that the
level-`n+1` higher principal units are contained in those at `k`.

The class map `standardLubinTateUnitParameterClass F n` is by definition
the quotient homomorphism `QuotientGroup.mk'` with kernel the level-`n+1`
group, and `standardLubinTateUnitParameterSubgroup F n k` is the image
(`Subgroup.map`) of the level-`k` group under it. A `change` step
rewrites membership of the class of `u` in that image as membership of
`u` in its preimage (`Subgroup.comap`), which holds definitionally.
Mathlib's `QuotientGroup.comap_map_mk'` identifies this preimage with the
supremum of the kernel and the level-`k` group, and `sup_eq_right`
together with the containment just proved reduces the supremum to the
level-`k` group, giving the claimed membership equivalence.

This direct proof replaces the source's use of the abstract
`AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff`
applied to `higherPrincipalUnitGroup.toPrincipalUnitFiltration`.
Neither M120.082 nor M231.020 is imported or duplicated. No extra
hypothesis, global instance or axiom is added.

## Source and modifications

Original source: Naganori Yamaguchi, NYLL
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean`,
M363.002, lines 42–58, with signature and conclusion at 42–48;
section/universe context at 22–29. Pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`; file SHA-256
`0205d0dc5727b940c1ca25159ddc4ba008423ec44a19e8d7ae024a8a9f6e1aa1`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 299 extracted the theorem, prefixed its namespace by
`Langlands.NYLL`, restated its conclusion through the separate exact
Prop-valued target and replaced its proof by the Mathlib argument above.
The imports are the target and `Mathlib.GroupTheory.QuotientGroup.Basic`.
The original copyright and author header remain; the Apache-2.0 license
and attribution are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
