# The spectral-norm topology on a finite extension of a local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` in Mathlib's sense (`IsNonarchimedeanLocalField`, with a `ValuativeRel`) and a finite extension `L/K`, the file equips `L` with the spectral norm extending a norm on `K`, and shows that `L` is then itself a nonarchimedean local field whose valuation extends that of `K`. Every structure is an explicit definition, so that the fields of a tower can all carry the norm defined from the same base.

## Definitions

- `localFieldNontriviallyNormedField K`: a nontrivially normed field structure on `K` from its valuation and a rank-one embedding of the value group into `ℝ≥0`; `localFieldIsUltrametricDist` shows the norm is ultrametric.
- `finiteExtensionSpectralNormedField K L`: `L` with Mathlib's spectral norm over this `K`.
- `finiteExtensionSpectralValuativeRel K L`: the valuative relation on `L` given by that norm.
- `finiteExtensionSpectralNormedAlgebra K E L`: for a tower `K → E → L` of finite extensions, `L` as a normed `E`-algebra with both spectral norms.

## Results

- `finiteExtensionSpectralCompleteSpace`, `finiteExtensionSpectralLocallyCompactSpace`, `finiteExtensionSpectralIsUltrametricDist`: for the spectral norm, `L` is complete, locally compact and ultrametric.
- `finiteExtensionSpectralIsNonarchimedeanLocalField`: with the spectral norm and its valuative relation, `L` is a nonarchimedean local field.
- `finiteExtensionSpectralValuation_hasExtension`: the valuation of `L` extends that of `K`.
- `finiteExtensionSpectralValuation_hasExtension_of_tower`: in a tower `K → E → L`, the valuation of `L` extends that of `E`.

## Proofs

Local compactness is Mathlib's theorem `LocallyCompactSpace.of_finiteDimensional_of_complete`, applied to `L` as a finite-dimensional normed space over `K`. The extension statements compare unit balls: the spectral norm restricts to the norm of `K` (`spectralNorm_extends`) and is compatible with towers (`spectralNorm.eq_of_tower`).

## Watch for

- The rank-one embedding for `K` is picked from `IsRankLeOne.nonempty.some`, so the absolute value of `K` is normalized by choice, not as `q^(-v)`.
- The statements concern these explicit structures, passed by `letI`, not instances found by search.
- `L/K` is only assumed finite, not separable.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean`: the Lean file is the source byte for byte (SHA-256 `5712f56772148c9102d16a29358380f9b3485f42fc06a836291c22c40f26d959`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
