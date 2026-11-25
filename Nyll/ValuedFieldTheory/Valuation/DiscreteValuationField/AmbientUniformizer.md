# Recognizing a uniformizer through an embedding into a larger complete discretely valued field

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AmbientUniformizer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be finite separable, with a complete discrete valuation on `L` extending one on `K`, and let `ι : L → M` be a field embedding into another complete discretely valued field. The file shows that an element of `L` whose image is a uniformizer of `M` is already a uniformizer of `L`, and gives the maps of valuation rings and residue fields induced by `ι`.

## Main definitions and results

- `valuationSubringMapOfIsEquivComap`: for valuations `vL` on `L`, `vM` on `M` and `ι : L →+* M` such that `vL` is equivalent to the pullback of `vM` along `ι`, the restriction of `ι` to valuation rings; `valuationSubringMapOfIsEquivComap_isLocalHom`: it is a local homomorphism.
- `residueFieldMapOfIsEquivComap`: the induced map of residue fields; `residueFieldMapOfIsEquivComap_mapEquiv`: it commutes with the residue automorphisms induced by automorphisms `σL`, `σM` of the valuation rings that are compatible with `ι`.
- `isUniformizer_of_ambient_image_isUniformizer`: let `base`, `target`, `ambient` be complete discretely valued fields on `K`, `L`, `M`, with the valuation of `target` extending that of `base`, and with the pullback of the valuation of `ambient` along `ι` also extending that of `base`. If `ι π` is a uniformizer of `M`, then `π` is a uniformizer of `L`.

## Proof

Uniqueness of the extension of a complete discrete valuation to a finite separable extension, proved elsewhere in the library, makes the valuation of `L` equivalent to the pullback of that of `M`. Then `π` has valuation `< 1`, and any `a` in the maximal ideal of `L` is `π` times an element whose image, `ι(π⁻¹ a)`, is integral in `M`; so `π` generates the maximal ideal.

## Points to watch

- `CompleteDVF` is the library's own structure for a complete discretely valued field, not a Mathlib class.
- The hypothesis that the pullback along `ι` extends the base valuation is an instance argument `HasExtension`; it is not derived from a compatibility of `ι` with `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AmbientUniformizer.lean`: the Lean file is the source byte for byte (SHA-256 `ee310e88555ff9916ef748b8c527e8820d320c6c29f343d77ec1e28bb6716489`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
