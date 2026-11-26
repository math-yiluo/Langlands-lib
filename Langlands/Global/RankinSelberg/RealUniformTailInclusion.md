# Uniform real Whittaker models of block lists inside character-list models

Module `Langlands.Global.RankinSelberg.RealUniformTailInclusion`. Every declaration is proved,
with no axioms beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

The module proves that the uniform Whittaker model `realUniformWhittakerModel r ds a` of a real
block list `ds` lies in the uniform Whittaker model of a list `L` of real characters. `L` has the
same rank and is a permutation of the expanded list `RealPrincipalSeries.expand ds`. It then
derives both uniform continuation targets from character-list growth alone, without the
principal-series inclusion premise `RealUniformPrincipalSeriesInclusionStatement` used in
`RealLocalCharacterGrowthInterfaces`. The character list `L` differs from `expand ds` only in the
order of the two characters of each induced block of nonzero weight. Pair `L`-factors,
`ε`-factors and the determinant do not depend on that order.

## Surjective exact intertwiners

`realUniformWhittakerModel_le_of_intertwiner a q hq hs`: let `q` be a linear map from the
compact-finite standard module of `ds'` to that of `ds` (both of rank `r + 1`). Assume `q` is an
exact intertwiner, `IsRealIntertwinerModulo (r + 1) ds' ds ⊥ q`: it commutes with right
translation by `O(r + 1)` and with every right derivative. Assume also that `q` is surjective. Then
`realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r ds' a`.

Proof. The model of `ds` is the supremum of the ranges of uniform Whittaker maps
`B` (`IsRealUniformWhittakerIntertwiner r ds a B`). For such `B`, the composite `B ∘ q` is a
uniform Whittaker map for `ds'`:

- the unipotent covariance, smoothness and polynomial growth of `B (q f)` are those of `B` at
  `q f`;
- the common growth exponent of `B` serves for `B ∘ q`;
- compact equivariance and Lie compatibility follow from the same properties of `B`, applied to
  `q f`, and the intertwining identities `q (k · f) = k · q f`, `q (D_X f) = D_X (q f)`. These are
  read off from `hq`, since the difference lies in the zero submodule.

Surjectivity of `q` gives `range (B ∘ q) = range B`.

## Counting and splitting

- `nonzeroInducedCount ds`: the number of induced blocks of `ds` with nonzero weight;
  `nonzeroInducedCount_append` says that it is additive.
- `weight_eq_zero_of_nonzeroInducedCount_eq_zero`: if the count is zero, every induced block
  found by `realInducedBlockAt` has weight zero. The proof follows the recursion of
  `realInducedBlockAt`.
- `exists_split_of_nonzeroInducedCount_ne_zero`: if the count is nonzero, then
  `ds = pre ++ [induced d] ++ post` with `d.weight ≠ 0`.
- `expand_append'`, `expand_induced_single`, `expand_character_pair`: expansion is additive. It
  sends `[induced d]` to `[character (ca d (positionParity ℓ)), character (cb d 0)]`, with
  `ℓ = |weight d|`, and fixes a pair of characters. Here `ca d sa = charData sa (t + ℓ/2)` and
  `cb d sb = charData sb (t - ℓ/2)`, with `t` the exponent of `d` (module
  `RealInducedCharacterMaps`). The second and third lemmas hold by definition.
- `positionParity_val k`: `(positionParity k).val = (k + 1) % 2`.

## The inclusion

`RealUniformCharacterListInclusionStatement r`: for every block list `ds` with
`realRank ds = r + 1` and every `a : ℝˣ`, there is a list `L` with

- `IsRealCharacterList L`;
- `L.Perm (expand ds)`;
- `realRank L = r + 1`;
- `realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r L a`.

`realUniformCharacterListInclusion r` proves it. `exists_characterList_model_le` proves it by
induction on `nonzeroInducedCount ds`:

- Count zero. Take `L = expand ds`. It is a character list (`isRealCharacterList_expand`) of the
  same rank (`realRank_expand`). Since every induced weight is zero, the Library's
  `realUniformWhittakerModel_expand_of_zero_weights` gives equality of the two models.
- Count `k + 1`. Split `ds = pre ++ [induced d] ++ post` with `ℓ = |weight d| > 0`. Put
  `ds' = pre ++ [character (cb d 0), character (ca d (positionParity ℓ))] ++ post`. It has
  the same rank (`realRank_tail_mid`) and count `k`. The parity condition of the tail maps,
  `(positionParity ℓ + 0) % 2 = (ℓ + 1) % 2`, is `positionParity_val`. The Library's tail map
  `blockFrobMap (data_tail hr hl hs)` from the compact-finite standard module of `ds'` onto that
  of `ds` is an exact intertwiner (`modulo_tail`) and surjective (`tail_surjective`). By
  `realUniformWhittakerModel_le_of_intertwiner`, the model of `ds` lies in that of `ds'`. The
  induction hypothesis for `ds'` gives `L`. Finally, `expand ds'` is
  `expand pre ++ [character (cb d 0), character (ca d _)] ++ expand post`, and `expand ds` is the
  same list with the two middle characters swapped (`List.Perm.swap`).

## The continuation targets

- `determinant_perm`: `RealJacquet.determinant` (a product in `ℂˣ`) is invariant under
  permutations.
- `realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth`: if
  `RealLocalEqualCharacterGrowthAtRank r` holds for every `r > 0`, then
  `RealLocalUniformPositiveEqualContinuationStatement` holds.
- `realLocalUniformUnequalContinuation_of_unequalCharacterGrowth`: if
  `RealLocalUnequalCharacterGrowthAtRanks r t h` holds for all `t < r`, then
  `RealLocalUniformUnequalContinuationStatement` holds.

Proof (equal rank; unequal rank is the same). Given block lists `ds`, `es` and `W`, `W'` in their
uniform models with characters `a`, `-a`, the inclusion gives character lists `L`, `L'` with `W`,
`W'` in their models. Character growth at `(L, L')` gives a normalized pair, and
`HasRealPairNormalizedGrowth.equalContinuation` gives the continuation package with the factors
of `(L, L')` and sign `det(L, -1)^r`. The Library's `realPairLFactor_perm` and
`realPairEpsilon_perm` (for `L ~ expand ds`, `L' ~ expand es` and their blockwise duals), together
with `determinant_perm` and `determinant_expand`, replace these by the factors of
`(expand ds, expand es)` and the sign `det(ds, -1)^r`. The Library's `continuationPackage_of_expand`
then passes to the factors of `(ds, es)`. That last step does not identify individual factors:
it uses `RealPrincipalSeries.pairMultiplier_expand`, by which the combined gamma multiplier of the
position expansion equals that of the block lists off a discrete set. The sign of the unequal target,
`det(ds, -1)^(t+1) · det(es, -1)`, is treated the same way.

- `RealGodement.RealLocalUniformPositiveEqualContinuationPremisesWithoutInclusionStatement`: the
  implication `RealUniformCanonicalRangePremise → RealCanonicalStandardEvaluationPremise →
  (∀ t, RealMatrixCoefficientGrowthPremise t) → (∀ t, RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t) →
  RealLocalUniformPositiveEqualContinuationStatement`. It is proved by
  `realLocalUniformPositiveEqualContinuation_of_premisesWithoutInclusion`, which combines the
  equal-rank theorem above with the Library's step `realLocalEqualGrowthStep` at each positive
  rank `t + 1`. Its four premises are not proved in this module.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, carries out the induction of §§8–10 for
representations induced from characters and passes to general generic representations in §11
(pp. 81–82, Proposition 11.1 on p. 82). There the induced representation `I_{σ,u}` is a
subrepresentation of a principal series `I_{μ,v}`, and Lemma 2.4 (p. 9), the extension of
continuous Whittaker forms along closed invariant subspaces, shows that the Whittaker form of
`I_{μ,v}` restricts to a nonzero form on `I_{σ,u}`. This module uses instead the Library's
explicit surjective intertwiners onto the standard modules with induced blocks. Each discrete
series block of weight `ℓ` is a quotient of the principal series of its two position characters
in the opposite order, through the tail multiplier of `RealBlockMultiplier`. This gives the
inclusion of Whittaker models directly. Permutation invariance identifies each pair `L`-factor,
including the factor of the dual lists, and the pair `ε`-factor of the character list with those
of the position expansion. The individual factors of the position expansion differ in general
from those of the block lists; the transfer to the block lists uses
`RealPrincipalSeries.pairMultiplier_expand`, which preserves the combined gamma multiplier off a
discrete set. In the proof of Proposition 11.1, Jacquet likewise writes the block `L`-factor as a
polynomial multiple of the product of the character factors (Appendix, Lemma 16.1, p. 112) and
uses that the gamma factors agree. The holomorphy of the quotient by the block `L`-factor, also
proved in §11, is neither needed nor proved here.
