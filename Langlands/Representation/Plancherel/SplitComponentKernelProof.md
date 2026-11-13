# The norm kernel of a split component (Renard V.2.6, Lemma, proof)

Author: Worker 114 (Task 5679, `cce59833-87fe-4fa2-bd38-c532167817a0`).

`Langlands.Plancherel.RenardCartan.splitComponentKernel` proves exactly the
published proposition
`Langlands.Plancherel.RenardCartan.SplitComponentKernelStatement.{u}`
(module [`RenardLatticeComparisonStatement`](RenardLatticeComparisonStatement.md)),
at every universe `u`, with no added hypothesis. The statement's Lean/Markdown
pair and everything it imports are unchanged.

## Statement

For every nonarchimedean local field `F : Type u` (with the Library's field,
`ValuativeRel`, topology and `IsNonarchimedeanLocalField` instances, in either
characteristic), every actual connected reductive group scheme `Z` over
`Spec F`, every actual commutative group scheme `T` and every
`s : T.toGrp ⟶ Z` with `IsSplitComponent s`:

`(rationalCommonNormKernel Z).comap (rationalPoints.map s) = rationalCommonNormKernel T.toGrp`.

That is, a point `t ∈ T(F)` has `|χ(s(t))|_F = 1` for every rational character
`χ` of `Z` if and only if `|α(t)|_F = 1` for every rational character `α` of `T`.

## Implemented proof

The module contains three theorems.

- `comap_rationalCommonNormKernel_le_of_finiteIndex s hindex` proves the
  inclusion `comap ≤ rationalCommonNormKernel T.toGrp` for any morphism
  `s : T.toGrp ⟶ Z` whose character restriction
  `characterRestrict s : X^*(Z)_F →+ X^*(T)_F` has finite-index range. Let `t`
  lie in the pullback and let `α` be a rational character of `T`.
  1. Both norm kernels are rewritten in valuation form by the published
     `mem_rationalCommonNormKernel_iff_valuation`: membership means that every
     integer coordinate `v(·)(χ)` of `rationalCharacterValuation` vanishes.
  2. With `N` the index of the range of `characterRestrict s` (nonzero by
     `AddSubgroup.FiniteIndex.index_ne_zero`), Mathlib's
     `AddSubgroup.nsmul_index_mem` gives a rational character `ψ` of `Z` with
     `characterRestrict s ψ = N • α`.
  3. The published compatibility `rationalCharacterValuation_characterRestrict`
     gives `v(t)(characterRestrict s ψ) = v(s(t))(ψ)`. The left side is
     `N • v(t)(α)` by additivity (`map_nsmul`), and the right side is `0`
     because `s(t)` lies in the norm kernel of `Z`.
  4. `N • v(t)(α) = 0` in `ℤ` with `N ≠ 0` gives `v(t)(α) = 0`
     (`smul_eq_zero`).
- `comap_rationalCommonNormKernel_eq_of_finiteIndex` combines this with the
  published `rationalCommonNormKernel_le_comap s` (Worker 200), which gives the
  reverse inclusion for every morphism.
- `splitComponentKernel` introduces `F`, `Z`, `hZ`, `T`, `s`, `hs` and applies the
  previous theorem. Finite index of the restriction range is the published
  `IsSplitComponent.finiteIndex_range_characterRestrict hZ`
  (module `Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex`,
  Worker 1001), which uses connected reductivity of `Z` and the split-component
  property of `s`.

The inspected axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the literature

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, V.2.6,
Lemma, first assertion `⁰A_G = ⁰G ∩ A_G` (printed page 108 / PDF page 114).
Renard's proof takes `g ∈ ⁰G ∩ A_G` and `χ ∈ X^*(A_G)`, uses that some power
`χ^m` (`m ≥ 1`) lies in `X^*(G)`, and concludes `|χ(g)|^m = 1`, hence
`|χ(g)| = 1`; the reverse inclusion is called clear. The Lean proof follows
this route with the integer valuation coordinates in place of absolute values
and with the index of the restriction range as the exponent. The finite-index
input is taken from the Library rather than re-derived from Renard's argument
through `G/𝒟G`.

## Scope

This proves only `SplitComponentKernelStatement`. The finite-representative
statement `FullLatticeRepresentativeStatement` is proved in
[`FullLatticeRepresentativeProof`](FullLatticeRepresentativeProof.md), and
`SplitComponentLatticeStatement` in
[`SplitComponentLatticeProof`](SplitComponentLatticeProof.md). The remaining
assertions of the V.2.6 Lemma and Proposition are not addressed here.
