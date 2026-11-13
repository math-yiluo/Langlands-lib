# From the rank-one statement to the class sums of `M/L`

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Galois groups of `M/L` inside `Gal(M/F)`

Fix `L ⊆ M` as in `SpectralConductorInduction`. `algebraL`, `algebraLM` and `towerLM`
are the algebra structures used by `CommonClosureRankOneConductorStatement`: the
`ℚ_p`-structure of `L.asPadicField`, and `M` over `L` through the actual inclusion.

- `galLtoF`: an `L`-automorphism of `M` is an `F`-automorphism with the same
  underlying ring map. It lands in `fixingM` (`galLtoF_mem_fixingM`) and is injective
  (`galLtoF_injective`). `galFtoL` inverts it on `fixingM`
  (`galLtoF_galFtoL`).
- `integerAutomorphism_galLtoF`: both act on the integer ring of `M` by the same map
  (proved by `rfl`). Consequently `mem_inertia_iff` holds: `σ` lies in the inertia
  group of `M/L` iff its image lies in that of `M/F`. So does
  `mem_lowerRamificationGroup_iff`: `σ` lies in the `i`th lower group of `M/L` iff
  its image lies in the `i`th lower group of `M/F`. This is
  Serre, *Local Fields*, IV §1, Proposition 2 (`H_i = G_i ∩ H`), printed p. 62
  (PDF p. 69); here it holds by construction. Hence
  `galoisLowerCount_galLtoF` (equal counts) and `lowerBound_spec_L` (the bound of `M/F`
  also bounds the lower groups of `M/L`).

## Descent of a presented character

Let `χ` be presented at `M` (`IsPresentedAt F M L χ`).

- `inertiaLtoM` maps inertia of `M/L` into inertia of `M/F`.
- `descendedCharacter χ hχ` is the character `σ ↦ χ(liftL (image of σ))` of the
  inertia group of `M/L`. It is multiplicative, and `1` goes to `1`, because a presented
  character takes equal values on inertia elements with equal restriction.
- `descendedCharacter_compat`: it satisfies the hypothesis of the rank-one statement.
  If `w ∈ W_L` is in inertia and `σ` acts on `M` as the Galois image of `w`, then
  `restrictionM w` is the image of `σ`, so `χ(w)` equals the descended value.
- `trace_rankOneCharacterRepresentation`: `dim - tr = 1 - ρ(σ)` on the line.
- `inertiaArtinConductor_descendedCharacter`: the Artin expression of the descended
  character equals `lClassSum F M L hLM χ`. Proof: the inertia class-sum formula
  (module `SpectralConductorFunctional`) with the bound `lowerBound F M`.
  `Finset.sum_bij_ne_zero` along `inertiaLtoM` reindexes the sum; its image is exactly
  the inertia elements of `M/F` fixing `L`. The cardinalities agree through the
  bijection with `inertiaL`.
- `lClassSum_eq_characterConductor`: under `CommonClosureRankOneConductorStatement F`
  and `NormalizedReciprocity F e`, `lClassSum χ = a(fieldCharacterEquiv F e L χ)`.
  Apply the statement to the descended character.
