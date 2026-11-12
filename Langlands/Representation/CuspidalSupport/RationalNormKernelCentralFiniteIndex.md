# Finite index of the actual norm kernel joined with the centre

This internal helper module proves one theorem,
`Langlands.CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex`. It has a single universe parameter `u`.

## Statement

For every field `F : Type u` with `ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`, every group scheme `G` over `Spec (CommRingCat.of F)` and every certificate `hG : GroupScheme.IsConnectedReductive G`, the subgroup

`Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (GroupScheme.rationalPoints G)`

of the rational-point group has finite index (`Subgroup.FiniteIndex`). Here `Plancherel.rationalCommonNormKernel G` is the actual common kernel of the normalized rational-character norms, Renard's `⁰G`. The statement is purely group-theoretic, so no topology on the point group is involved.

## Provenance

This is a derived internal result. It is the finite-index input of the published generic assembly `normKernelTwistEquivalence_of_finiteIndex_scalar` (module `NormKernelTwistEquivalence`), which `RationalNormKernelTwistEquivalenceProof` applies to prove Renard VI.3.2(iii). The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The split component `A_G` ("composante déployée") is defined in V.2.1 (printed p.104 / PDF p.110), and `⁰G` in V.2.3 (printed pp.105–106 / PDF pp.111–112). Subsection V.2.6 begins on printed p.107 / PDF p.113. Its Proposition (printed p.108 / PDF p.114) states that `G/⁰G A_G` is finite. The proof uses the preceding Lemma on the same page: restriction of rational characters to `A_G` is injective with finite-index image. Since `A_G` is central, finiteness of `G/⁰G Z(G)` follows at once. That last step is the derived part. The Lean proof below follows the same route.

## Proof

The proof combines four published results.

1. `GroupScheme.splitComponentStatement F G hG` (Renard V.2.1) gives a commutative group scheme `A` and a split component `s : A.toGrp ⟶ G` with certificate `hs : IsSplitComponent s`.
2. `GroupScheme.characterRestriction F G hG A s hs` shows that restriction of rational characters along `s` is injective. `Plancherel.RenardCartan.finiteIndex_splitValuationImage_of_injective hG s hs` turns this injectivity into finite index of the split-torus valuation image `Plancherel.RenardCartan.splitValuationImage s`.
3. A split component is a central split torus, so `hs.isCentralSplitTorus.isCentral` is centrality of `s`. `Plancherel.finite_rationalCentralQuotient` then shows that the quotient of the point group by `rationalCommonNormKernel G ⊔ (GroupScheme.rationalPoints.map s).range` is finite. Mathlib's `Subgroup.finiteIndex_of_finite_quotient` converts this into finite index of that subgroup.
4. The range of the point map of a central morphism lies in the centre (`hs.isCentralSplitTorus.range_le_center`). So the subgroup from step 3 is contained in `rationalCommonNormKernel G ⊔ center`, and `Subgroup.finiteIndex_of_le` with `sup_le_sup_left` transfers finite index to the larger subgroup.
