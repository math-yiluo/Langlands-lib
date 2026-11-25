# Laurent series coordinates on the field of norms

Module `FontaineWintenberger.FieldOfNorms.Structure.Laurent`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`, and let `κL` be the residue field of the integral closure of `𝒪[K]` in `L`. For every element `u` of the field of norms with valuation `exp(−1)`, the file identifies `FieldOfNorms K L` with the field of Laurent series over `κL`, sending the variable to `u`.

## Main definitions

- `FieldOfNorms.powerSeriesEquiv K L u hu : PowerSeries κL ≃+* (valuation ring of the field of norms)`.
- `FieldOfNorms.laurentEquiv K L u hu : LaurentSeries κL ≃+* FieldOfNorms K L`.

Both are obtained by applying the general constructions `valuedPowerSeriesEquiv` and `laurentUniformizerEquiv` (for a complete discretely valued field with a coefficient homomorphism) to the homomorphism `residueConstantsIntegerHom K L` and the residue isomorphism `FieldOfNorms.residueEquiv K L`.

## Main results

- `powerSeriesEquiv_C`, `powerSeriesEquiv_X`: constants go to `residueConstantsIntegerHom K L a`, and `X` goes to `u`.
- `laurentEquiv_powerSeries`, `laurentEquiv_C`, `laurentEquiv_X`: the Laurent isomorphism extends the integral one; constants go to `residueConstantsFieldEmbedding K L a`; `X` goes to `u`.
- `laurentEquiv_valuation`: the valuation of the field of norms at the image of `A` equals the `X`-adic valuation `Valued.v A`, for every Laurent series `A`.
- `powerSeriesEquiv_valuation`: for a nonzero power series `A`, the image has valuation `exp(−order A)`.
- `uniformContinuous_laurentEquiv`, `uniformContinuous_laurentEquiv_symm`, and the corresponding continuity statements: the isomorphism and its inverse are uniformly continuous.
- `continuous_powerSeriesEquiv`: the integral isomorphism is continuous, for the power-series topology with discrete coefficients.
- `laurentEquiv_unique`: a continuous ring homomorphism from `LaurentSeries κL` to the field of norms that agrees with `residueConstantsFieldEmbedding` on constants and sends `X` to `u` equals `laurentEquiv`.

## Points to watch

- The coefficient field is `κL`, the residue field of `L`, embedded by the library's own map `residueConstantsFieldEmbedding`; the file's comments say this embedding includes an inverse-Frobenius normalization.
- The isomorphism depends on the choice of `u`; any element of valuation `exp(−1)` is allowed.
- `κL` is given the discrete uniformity locally, by `letI`, inside each statement.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Laurent.lean` (SHA-256 of the source file `428257a3d257dfc9dbed80f6a80211c47ffffce690031458454ea8abbf8fb7dd`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
