# The central torus quotient from its prerequisites

Author: Worker 1428. Rechecked by Worker 1404.

This module proves two theorems.

- `Langlands.GroupScheme.SubgroupFunctor.isNormal_of_le_center`: a subgroup
  functor `N` of a group scheme `G` over any base with `N ≤ center G` is
  normal. For a point `x` of `N` and any point `g` of `G` over the same test
  scheme, `x` commutes with `g` (`commute_of_mem_center`), so
  `g * x * g⁻¹ = x` lies in `N`.
- `Langlands.GroupScheme.splitCentralTorusQuotient_of_prerequisites`: the
  proposition `SplitCentralTorusQuotientStatement.{u}` follows from four
  prerequisite propositions, taken as explicit hypotheses:
  - `h1 : SplitTorusKernelCentralityStatement.{u}` (statement task
    `6dae7832-cc0b-4fe7-8a6f-18206d4999a9`);
  - `h2 : CentralQuotientReductiveStatement.{u}` (statement task
    `40dacb91-f422-43f1-afd8-9ca7b7ce22d4`);
  - `h3 : SplitTorusIsogenyOfLatticeMapsStatement.{u}` (statement task
    `6434528b-03d5-4d04-b22c-795071bdc773`);
  - `h5 : CentralIsogenyMaximalTorusImageStatement.{u}` (statement task
    `3898521e-56d5-4383-a30d-af7854721d93`).

The theorem is conditional: it does not prove the four hypotheses. The four
statements are published (Library commit
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`). The final proof
`Langlands.GroupScheme.splitCentralTorusQuotient`
(module `Langlands.GroupScheme.Reductive.CentralTorusQuotientProof`) does not
apply this theorem: it applies the variant
`splitCentralTorusQuotient_of_prerequisites'`
(module `Langlands.GroupScheme.Reductive.CentralTorusQuotientFiniteReduction`),
which follows the same proof without `h2` and imports this module for
`SubgroupFunctor.isNormal_of_le_center`.

## The proof

Fix a field `k`, a connected reductive `G`, split tori `T` and `T'`, a
maximal torus `i : T ⟶ G`, and `t : T ⟶ T'` with injective character and
cocharacter maps such that every root of `i` is `t ≫ α'`.

1. **`t` is an isogeny.** `h3` gives `IsIsogeny (groupHom t)`: the underlying
   morphism is finite, flat and surjective (and so quasi-compact).
2. **The finite central subgroup.** Let `ιN` be the composite of the actual
   kernel inclusion `CommGroupScheme.kernelι t` with `i`. It is central by
   `h1` and hence its range lies in `center G`
   (`isCentral_iff_range_le_center`). It is a closed subgroup: the kernel
   inclusion is a closed immersion because `T'` is affine, and `i` is a
   closed immersion because it is a maximal torus. Its source is finite over
   `Spec k`: the kernel square `kernel_isPullback_scheme` is a base change of
   the finite morphism `t`.
3. **The quotient.** The published
   `exists_centralIsogeny_of_finite_central_subgroup`
   (`CentralIsogeny/FiniteKernelQuotient.lean`) applies to `ιN`, with
   normality from `isNormal_of_le_center`. It gives a smooth affine `Q` and a
   central isogeny `q : G ⟶ Q` whose actual kernel has the same range as
   `ιN`. Flatness, surjectivity, local finite presentation and this kernel
   equality are `RelativeRoot.IsFppfQuotient (range ιN) q`. As the range of
   `ιN` lies in `center G`, `h2` shows that `Q` is connected reductive.
4. **The torus map.** Every point killed by `t` is killed by `i ≫ q`: it maps
   into the range of `ιN`, which is the kernel of `q`. So
   `kernelι (groupHom t) ≫ (i ≫ q) = 0` (`AffineQuotient.kernelι_comp_eq_zero`),
   and fpqc descent along `t` (`FpqcHomDescent.hom`, `GroupScheme/HomDescent.lean`)
   gives `i'' : T' ⟶ Q` with `groupHom t ≫ i'' = i ≫ q`.
5. **`i''` is a closed torus.** Conversely, a point `x` of `T` killed by
   `i ≫ q` has `x ≫ i` in the kernel of `q`, so `x ≫ i = y ≫ ιN` for a point
   `y` of the kernel of `t`; cancelling the monomorphism `i` puts `x` in the
   kernel of `t`. By `FpqcHomDescent.mono_of_kernel_range_le`
   (`MatrixRepresentation/UnipotentQuotient.lean`) the descended map `i''` is
   a monomorphism, and `IsTorus.isClosedSubgroup_of_mono`
   (`Torus/UnipotentQuotientClosed.lean`) makes it a closed subgroup.
6. **Maximality.** `h5`, applied to the central isogeny `q`, the maximal torus
   `i`, the closed torus `i''` and the surjective `t`, gives
   `IsMaximalTorus i''`.

The conclusion is `⟨Q, hQ, q, i'', hmax, hcq, hfac.symm⟩`.

## Provenance

The proof route is internal. It follows the mathematical sketch in the
Markdown of `SplitCentralTorusQuotientStatement` (Milne, *Algebraic Groups*,
2017, source `milne-2017-algebraic-groups`: 12.9, 21.7, 21.8, 5.14, 17.20,
20.1, with printed page locators there). Each step that is not a published
Library theorem is one of the four hypotheses, whose statement Markdown gives
its own source argument.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
against Library commit `0d12b7d171600d15516e52ee508d3aaca3e9cf9e` (diagnostic
`999bf037-7db0-47c1-9847-544c0146c39a`) and again against Library commit
`af00455e8e62bad8f10d229e6e3b908795bbf28f` (diagnostic
`f456f99c-c16f-4bae-8ea0-5bd235594b96`) and Library commit
`0bd5bf67c3464359bc8da3b3100163d6ee3da352` (diagnostic
`d36d4362-ae19-4303-b2e5-46bd5324db90`): 0 errors, 0 warnings, axioms
`propext`, `Classical.choice`, `Quot.sound`.
