# Character-list normalized-growth statements for the real induction

This module restricts the rank-indexed growth predicates of `RealLocalGrowthInterfaces` to
lists of one-dimensional real characters. It also reduces both uniform continuation targets
to the restricted predicates, keeping the uniform principal-series inclusion as an explicitly
named open premise.

## Why character lists

Let a block list contain an induced block `D_k` of rank two. Then normalized growth
normalized by the block factor `L(s, ds × es)` asserts that `Z / L(s, ds × es)` is entire.
That is Jacquet's Theorem 2.1 (ii) for discrete series. Jacquet does not prove it in the
induction of §§8–10, which treats representations induced from characters (the principal
series). He derives the general case afterwards, in §11 (Proposition 11.1, pp. 81–82). There
the block representation is a subrepresentation of a principal series, and the gamma factors
of the blocks and of their position characters agree. Holomorphy of the quotient is then
obtained from unitary parameters by analytic continuation. The statements here follow the
same order: the induction is stated for character lists. The block case comes back only at
the end, through the expansion `RealPrincipalSeries.expand`, which replaces each block by its
two real position characters. The continuation targets need only the functional equation,
not the holomorphy of the quotient by the block factor.

## Definitions

- `IsRealCharacterList ds`: there is a list `cs : List RealCharacterData` with
  `ds = cs.map RealBlock.character`.
- `RealLocalEqualCharacterGrowthAtRank r`: the body of `RealLocalEqualGrowthAtRank r`, with
  the two added hypotheses `IsRealCharacterList ds` and `IsRealCharacterList es`. The
  hypotheses come right after the two lists, before the rank equalities. The predicate keeps
  the integrals, dual lists, epsilon parameter `-a`, scale `sqrt |a|` and sign
  `det(ds, -1) ^ r` unchanged.
- `RealLocalUnequalCharacterGrowthAtRanks r t h`: the body of
  `RealLocalUnequalGrowthAtRanks r t h`, with the same two added hypotheses. Its sign is
  `det(ds, -1) ^ (t + 1) · det(es, -1)`.
- `RealLocalAdjacentCharacterGrowthAtRank r`: the unequal character statement at ranks
  `r + 1` and `r`.

## Theorems

- `IsRealCharacterList.nil`, `.cons`, `.append`, `.map_dualBlock`: the empty list is a
  character list. Character lists are closed under adding a character in front, under
  concatenation, and under `dualBlock` (which sends the character `c` to `c.inverse`).
- `isRealCharacterList_expand ds`: `expand ds` is a character list for every block list `ds`.
  The proof is by induction on `ds`. An induced block `d` with `k = |d.weight|` contributes the
  characters `charData (positionParity k) (d.exponent + k/2)` and
  `charData 0 (d.exponent - k/2)`, as in the definition of `expand`.
- `continuationPackage_of_expand ds es b c hc`: in a `ContinuationPackage` for two fixed
  functions `Z`, `Zd` and a fixed sign, the expanded factors can be replaced by the original
  block factors. These are the reciprocal pair `L`-factors of `expand ds`, `expand es` and of
  their duals, and the pair epsilon factor with parameter `b` and scale `c`. The proof is the
  same as that of the Library's `equationPackage_of_expand`. Off a discrete set both reciprocal
  `L`-denominators are nonzero, and `pairMultiplier_expand` identifies the two multipliers
  `ε · L(s) / L^∨(1 - s)`. The functional equation is cleared of the primal denominator,
  rewritten, and restored.
- `RealLocalEqualGrowthAtRank.toCharacter`, `RealLocalUnequalGrowthAtRanks.toCharacter`,
  `RealLocalAdjacentGrowthAtRank.toCharacter`: each block-list predicate implies its character
  restriction, by forgetting the added hypotheses.
- `realLocalEqualCharacterGrowthAtRank_zero`: rank zero of the equal character statement,
  restricted from `realLocalEqualGrowthAtRank_zero`.
- `realLocalUniformUnequalContinuation_of_characterGrowth`: assume
  `RealUniformPrincipalSeriesInclusionStatement` and unequal character growth at every pair
  of ranks. Then `RealLocalUniformUnequalContinuationStatement` holds. Given block lists `ds`,
  `es` and `W`, `W'` in their uniform models, the inclusion premise places `W`, `W'` in the
  uniform models of `expand ds`, `expand es`. These are character lists of the same ranks
  (`realRank_expand`). The growth hypothesis at the expanded lists gives the unequal
  continuation package for the expanded factors
  (`HasRealPairNormalizedGrowth.unequalContinuation`). Its sign equals the target sign by
  `determinant_expand`, and `continuationPackage_of_expand` returns to the block factors.
- `realLocalUniformPositiveEqualContinuation_of_characterGrowth`: the same argument with
  `HasRealPairNormalizedGrowth.equalContinuation`. It derives
  `RealLocalUniformPositiveEqualContinuationStatement` from the inclusion premise and equal
  character growth at every positive rank.

## Retained premise

`RealUniformPrincipalSeriesInclusionStatement` (Library module `RealPrincipalSeriesReduction`)
says that the uniform coefficient space of a block list lies in the uniform coefficient space
of its expansion. It is an explicit hypothesis of the two reductions above and is not proved
here. The Library reduces it to `RealUniformPrincipalSeriesExtensionStatement` by
`realUniformPrincipalSeriesExtensionReduction`.

## Provenance

These are internal statements organizing the induction in Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §§8–10, which is carried out for representations induced
from characters. The passage from character lists to blocks is the functional-equation part
of §11. In Lean it follows the Library's `realLocalUniformUnequalJacquet_of_principal`, with
continuation packages in place of equation packages. The predicates claim nothing by themselves; only the theorems listed above
are proved here.
