# Compact centre implies `⁰G = G(F)` (Renard V.2.6)

Author: Worker 103 (Task 5711, `8f1184cf-8c14-4ede-a502-96f1d8f66ec2`).

Module `Langlands.Representation.Plancherel.RationalNormKernelCompactCenterProof`.
The theorem `Langlands.Plancherel.rationalNormKernelCompactCenter` proves exactly the
published proposition
`Langlands.Plancherel.RationalNormKernelCompactCenterStatement.{u}` (module
[`RationalNormKernelRemarksStatements`](RationalNormKernelRemarksStatements.md)).
It holds at every universe `u` and adds no hypotheses.

## Statement

Let `F : Type u` be a nonarchimedean local field, of any characteristic, and `G` a
connected reductive group scheme over `Spec F`. Give `G(F) = GroupScheme.rationalPoints G`
the canonical `rationalPointTopology`. If the centre `Subgroup.center G(F)` is a compact
subset of `G(F)`, then `rationalCommonNormKernel G = ⊤`, that is, `⁰G = G(F)`.

## Implemented proof

1. **The centre lies in `⁰G`.** The published `compactSubgroup_le_rationalCommonNormKernel`
   (module `RationalCharacterTopology`) says that every compact subgroup of `G(F)` lies in
   `⁰G`. The reason is that each `g ↦ |χ(g)|_F` is a continuous homomorphism to a group
   whose only compact subgroup is trivial. Applied to the compact centre, it gives
   `Z(G(F)) ≤ ⁰G`.
2. **`⁰G` has finite index.** The published
   `CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex` (module
   [`RationalNormKernelCentralFiniteIndex`](../CuspidalSupport/RationalNormKernelCentralFiniteIndex.md))
   says that `⁰G ⊔ Z(G(F))` has finite index in `G(F)`, with no hypothesis on the centre.
   By step 1, `⁰G ⊔ Z(G(F)) = ⁰G`, so `⁰G` has finite index `n ≠ 0`.
3. **Torsion-freeness.** Let `g ∈ G(F)`. Since `⁰G` is normal of index `n`,
   `Subgroup.pow_index_mem` gives `g^n ∈ ⁰G`. By
   `mem_rationalCommonNormKernel_iff_valuation`, `⁰G` is the set of points whose
   valuation `rationalCharacterValuation G g`, an element of
   `Multiplicative (X*(G)_F →+ ℤ)`, is trivial. So for every rational character `χ`,
   `n • v(g)(χ) = 0` in `ℤ`, where `v(g)(χ)` is the `χ`-coordinate of the valuation of `g`.
   Since `n ≠ 0` and `ℤ` has no zero divisors (`smul_eq_zero`), `v(g)(χ) = 0` for every
   `χ`. Hence `g ∈ ⁰G`.

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to the literature

David Renard, *Représentations des groupes réductifs p-adiques* (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), V.2.6, Proposition
(printed p.108 / PDF p.114): « Le quotient `G/⁰G A_G` est fini, et `⁰G ∩ Z(G)` est
compact. Si `Z(G)` est compact, alors `⁰G = G`. » Renard's argument observes that a
compact centre forces `A_G = {1}`. Then `G/⁰G` is finite, and if `g^m ∈ ⁰G` then
`|χ(g)|_F^m = 1`, so `|χ(g)|_F = 1`.

The Lean proof follows the same outline with one change. Instead of showing that the split
component `A_G` is trivial, it uses V.2.3 (every compact subgroup lies in `⁰G`) to absorb
the whole compact centre into `⁰G`. The finite-index input from the Library is stated for
`⁰G ⊔ Z(G(F))`. It is derived there from a split component and the finite index of
`Λ(A_G)` in `Λ(G)`, so the Lean proof does not need `A_G = {1}`. The final step is Renard's
powers argument, written in the additive valuation coordinates `X*(G)_F →+ ℤ` instead of
the absolute values `|χ(g)|_F`.

## Scope

This proves only `RationalNormKernelCompactCenterStatement`. It does not prove the
published, still unproved V.2.6 Lemma `RenardCartan.SplitComponentKernelStatement`
(`⁰A_G = ⁰G ∩ A_G`), and it does not use it. The other two statements of the module are
proved in [`RationalNormKernelUnimodularProof`](RationalNormKernelUnimodularProof.md) and
[`RationalNormKernelRestrictionProof`](RationalNormKernelRestrictionProof.md).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements` | the target statement, `rationalCommonNormKernel`, `compactSubgroup_le_rationalCommonNormKernel`, `mem_rationalCommonNormKernel_iff_valuation` (through its imports) |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex` | `CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex` |
