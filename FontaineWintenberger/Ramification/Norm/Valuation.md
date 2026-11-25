# Valuations of norms in extensions of discrete valuation rings

Module `FontaineWintenberger.Ramification.Norm.Valuation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R → S` be a finite, local, injective extension of discrete valuation rings whose extension of fraction fields is separable, and let `f` be the residue degree (`inertiaDeg`) of the maximal ideal of `S` over `R`. The file proves that the normalized valuation of a norm is `f` times the normalized valuation of the element, on the rings and on the fraction fields.

## Main results

- `addVal_intNorm_uniformizer`: for a uniformizer `π` of `S`, the additive valuation of `Algebra.intNorm R S π` in `R` is `f`.
- `addVal_intNorm`: for every `x` in `S`, `addVal R (N x) = f * addVal S x`, with values in `ℕ∞`; the case `x = 0` is included.
- `intValuation_intNorm`: the same identity for Mathlib's multiplicative valuations at the maximal ideals: the valuation of `N x` is the valuation of `x` raised to the power `f`.
- `normalizedValuation_norm`: for fraction fields `K` of `R` and `L` of `S`, with `L/K` finite separable, the valuation of `Algebra.norm K x` in `K` is the valuation of `x` in `L` raised to the power `f`, for all `x` in `L`.
- `extensionValuationSubring_normalizedValuation_norm`: for a complete discretely valued field `K`, a finite separable extension `L/K` and a valuation `w` on `L` extending that of `K`, the same identity for the valuation ring of `w`, with exponent the degree of the residue field extension.
- `extensionValuationSubring_normalizedValuation_norm_of_residueDegree_one`: if that degree is 1, the norm preserves normalized valuations.

## Proofs

The case of a uniformizer comes from Mathlib's relative norm of ideals: the relative norm of the maximal ideal of `S` is the `f`-th power of the maximal ideal of `R` (`Ideal.relNorm_eq_pow_of_isMaximal`). The general case writes `x` as a unit times a power of a uniformizer. The statement on fields writes an element of `L` as a quotient of elements of `S`.

## Points to watch

- The extension need not be Galois or normal, and the residue fields need not be finite or perfect.
- Separability of the extension of fraction fields is assumed, in the first section in the form of an instance on `FractionRing R` and `FractionRing S`.
- Valuations on the fields are multiplicative, so the factor `f` appears as an exponent; the valuations are normalized on each field separately, so the ramification index does not appear.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Norm/Valuation.lean` (SHA-256 of the source file `e653b64c95690b6431e77e9a204d250e7f2a1c377d5753b6fc7cf292b7867edb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
