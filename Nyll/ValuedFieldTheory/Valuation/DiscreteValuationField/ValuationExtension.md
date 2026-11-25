# Extensions of valuations along field extensions

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file gives elementary facts about Mathlib's relation `Valuation.HasExtension` for a field extension `L/K`: how it behaves under equivalence and pullback, how a local map of valuation rings produces it, and how equivalence of valuations on `L` reduces to equality of valuation subrings. The first two results hold for arbitrary valuations on fields; in the others the valued fields are the library's complete discretely valued fields (`CompleteDVF`).

## Main results

- `hasExtension_of_isEquiv_base`: if `v₂` extends to `w` on `L` and `v₁` is equivalent to `v₂`, then `v₁` also extends to `w`.
- `hasExtension_comap_of_algebraMap_compatible`: if `v_K` extends to `v_M` on a `K`-algebra field `M`, and `ι : L →+* M` is compatible with the maps from `K`, then `v_K` extends to the pullback of `v_M` along `ι`.
- `valuation_hasExtension_of_local_valuationSubring_map`: for complete DVFs `K` and `L`, a local ring map `O_K → O_L` that agrees with `K → L` on elements makes the valuation of `L` an extension of that of `K`. `valuation_hasExtension_of_valuationSubring_equiv` is the case of a ring isomorphism `O_K ≃ O_L`.
- `comap_valuationSubring_eq_base` and `comap_valuationSubring_eq_base_of_hasExtension`: the valuation subring of any extension of the base valuation pulls back along `K → L` to the base valuation subring.
- `valuation_isEquiv_iff_valuationSubring_eq`, `valuation_isEquiv_iff_mem_valuationSubring` and one-directional forms: the valuation of a `CompleteDVF` on `L` is equivalent to another valuation `v'` exactly when the two have the same valuation subring, equivalently the same elements.

## Proofs

For the local-map criterion, if `z` is not in `O_K` then `z⁻¹` lies in its maximal ideal; locality sends it into the maximal ideal of `O_L`, so `z` cannot lie in `O_L`. The comparison results are Mathlib's `Valuation.isEquiv_iff_valuationSubring`.

## Caveats

The second form of the local-map criterion requires a ring isomorphism `O_K ≃ O_L` compatible with `K → L`, a much stronger hypothesis than the local map of the first form.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`: the Lean file is the source byte for byte (SHA-256 `d53d36300a2c71725395258ffd208d28df06cd12ae0afdc933743e736d4683b8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
