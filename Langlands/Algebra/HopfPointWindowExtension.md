# Extensions of Hopf points on principal opens where the weights lie in a window

Author: Worker 1421.

This module combines the weight-window openness of
`Langlands.Algebra.HopfPointWeightWindow` with the extension lemma of
`Langlands.Algebra.HopfPointExtension`. The result is the local extension used
in the chart construction of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. It is
an internal module with no literature counterpart. The background is
SGA 3, Exposé XI, §4 (registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`).

## Change of coefficients

For `ψ : C →ₐ[R] D`:

- `groupCounit_comp_mapAlgHom`, `mapAlgHom_comp_mapDomain`,
  `mapAlgHom_comp_pairMap`: the counit, `mapDomain` and the exterior square
  commute with `AddMonoidAlgebra.mapAlgHom M ψ`. Proved on single elements and
  pure tensors.
- `IsHopfPoint.mapAlgHom`: Hopf points push forward along coefficient maps.

## Windows

`V : Submodule R A` is finitely generated, with a coassociative coaction `δ`
lifting the comultiplication (see `HopfPointWeightWindow.exists_coaction`).
`β : A →ₐ[R] C[M']` is a Hopf point and `p` a prime of `C`.

- `exists_away_support_subset`: suppose the weights of the residue-field Hopf
  point at `p` lie in `T` (`WeightsIn`). Then some `f ∉ p` has the following
  property: for every `v ∈ V`, the coefficients of `β v` become supported in `T`
  after mapping to `Localization.Away f`. Proof: only finitely many weight
  projectors of `β` over `C` are nonzero (`exists_finite_weightsIn`). For each
  such weight outside `T`, `exists_mul_coeff_eq_zero` gives an element outside
  `p` that kills the corresponding coefficients. Let `f` be their product,
  which lies outside `p` because `p` is prime. The remaining weights outside `T`
  have vanishing projectors, hence vanishing coefficients (`counitV_proj`).
- `exists_away_extension`: suppose moreover that the generators `gen i` of a
  bounded presentation lie in `V`, that `π` is injective on
  `boundedSums s N`, and that the residue-field weights lie in `π '' s`. Then
  for some `f ∉ p` there is a unique Hopf point
  `α : A →ₐ[R] (Localization.Away f)[M]` with generator values supported in `s`
  and `mapDomain π ∘ α` equal to the localized `β`. This is
  `existsUnique_hopfPoint_extension` applied over `Localization.Away f`.

## Presentations

- `exists_isBoundedPresentation`: over a noetherian ring, a finite family of
  algebra generators has a degree bound `N ≥ 1` making it an
  `IsBoundedPresentation`. The kernel of `aeval` is finitely generated, since a
  polynomial ring in finitely many variables over a noetherian ring is
  noetherian. Each `Δ (gen i)` is a finite sum of pure tensors whose factors
  have chosen polynomial preimages (`Function.surjInv`). `N` is the maximum of
  the degrees involved and `1`.
