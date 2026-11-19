# Finite products of line bundles are locally free of finite rank

This internal module shows that a finite categorical product of line bundles is
locally free of rank the number of factors. All schemes lie in one universe
`u`.

## Results

- `restrictUnitIsoOfLE`: a trivialization `M|_V ≅ 𝒪_V` of a module sheaf on an
  open `V` restricts to a trivialization on every open `U ≤ V`. It uses
  Mathlib's restriction comparisons `restrictFunctorCongr`,
  `restrictFunctorComp` and `restrictUnitIso`.
- `piUnitFreeIso Y J`: for a finite type `J`, the product of `J` copies of the
  structure sheaf of `Y` is isomorphic to the free sheaf
  `SheafOfModules.free (ULift (Fin (card J)))`. Sheaves of modules form a
  preadditive category with finite products, hence with finite biproducts. The
  product is the biproduct, which is the coproduct (`biproduct.isoProduct`,
  `biproduct.isoCoproduct`). The coproduct is reindexed along
  `J ≃ Fin (card J) ≃ ULift (Fin (card J))`.
- `piRestrictFreeIso`: if every factor `L j` is trivial on an open `U`, then the
  restriction to `U` of the product is free with `card J` generators.
  Restriction is isomorphic to pullback (`restrictFunctorIsoPullback`).
  Pullback is additive, so it preserves finite products
  (`PreservesProduct.iso`).
- `isLocallyFreeOfRank_pi`: for a finite type `J` and line bundles
  `L : J → LineBundle X`, the product `∏ᶜ (L j).obj` is locally free of rank
  `card J` (`IsLocallyFreeOfRank`). For each point, intersect trivializing
  neighbourhoods of all factors (a finite infimum of opens) and apply the
  published criterion `isLocallyFreeOfRank_of_freeNeighborhoods`.
- `hasFiniteLocalBasis_of_isLocallyFreeOfRank`: fixed finite local rank gives
  finite local bases (`HasFiniteLocalBasis`): the same covering family of
  bases has index types equivalent to `Fin n`, hence finite.

## Provenance

Internal; standard facts assembled from Mathlib and the published Library
definitions `LineBundle`, `IsLocallyFreeOfRank` and `HasFiniteLocalBasis`.
