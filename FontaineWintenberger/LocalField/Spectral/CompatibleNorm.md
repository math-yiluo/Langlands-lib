# The norm attached to a discrete valuation

Module `FontaineWintenberger.LocalField.Spectral.CompatibleNorm`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a field with a `Valued K Γ` structure whose valuation `v` is rank-one discrete (`Valuation.IsRankOneDiscrete`). The file equips `K` with a norm compatible with `v`, so that results of the library stated for normed fields apply to fields given by a valuation, and transfers several of them: the discrete valuation ring property, Henselianity, and generation of the integer ring of a finite extension by one element.

## Main definition

- `discreteValuedNormedField K Γ`: the `NontriviallyNormedField` structure on `K` given by Mathlib's `Valued.toNontriviallyNormedField`, for the rank-one structure with base `2`. It is a definition, not a global instance; inside the file it is used as a local instance.

## Main results

- `discreteValued_norm_le_iff`: `‖x‖ ≤ ‖y‖ ↔ v x ≤ v y`.
- `discreteValued_valuationSubring`: the unit ball `𝒪[K]` of the norm equals `v.valuationSubring`.
- `discreteValued_uniformSpace`: the uniform structure of the norm is the valued one, by `rfl`; `discreteValued_completeSpace`: completeness is therefore the same.
- `discreteValued_unitBall_isDiscreteValuationRing`, `discreteValued_isCompleteDiscreteValuedField`: if `v.valuationSubring` is a discrete valuation ring, so is `𝒪[K]`; if moreover `K` is complete, `K` with this norm satisfies `IsCompleteDiscreteValuedField`.
- `discreteValued_henselianLocalRing`: under the same hypotheses, `v.valuationSubring` is a Henselian local ring.
- `discreteValued_spectral_hasExtension` (an instance): for `K` complete and `L/K` algebraic, the spectral valuation `spectralValuation K L` extends `v`.

For a field extension `L/K` and a valuation `w` on `L` with `v.HasExtension w`:

- `discreteValued_norm_hasExtension`: `w` also extends the norm valuation of `K`.
- `discreteValued_extension_isDiscreteValuationRing`, `discreteValued_extension_henselianLocalRing`: if `K` is complete, `v.valuationSubring` is a discrete valuation ring and `L/K` is finite separable, then `w.valuationSubring` is a Henselian discrete valuation ring.
- `discreteValued_extension_exists_generator`: if moreover the residue field of `v` is perfect, there is `x` in `w.valuationSubring` with `Algebra.adjoin v.valuationSubring {x} = ⊤`.
- `discreteValued_spectral_exists_generator`: the same for the spectral integer ring `spectralIntegerRing K L`.

## Proofs

Each statement is obtained from its normed counterpart (`unitBall_henselianLocalRing`, `extensionValuationSubring_isDiscreteValuationRing`, `extensionValuationSubring_henselianLocalRing`, `extensionValuationSubring_exists_generator`) by rewriting along the equality of valuation rings. For the generator, polynomials are transported along the ring isomorphism induced by that equality.

## Points to watch

- The norm depends on the choice of base `2`; only the order relation between norms and values is used.
- The value group `Γ` is arbitrary; discreteness is the class `Valuation.IsRankOneDiscrete`. That `v.valuationSubring` is a discrete valuation ring is a separate instance hypothesis where it is needed.
- No finiteness of the residue field is assumed; the generator statements need a perfect residue field and a finite separable extension.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/CompatibleNorm.lean` (SHA-256 of the source file `181eea24b260f34d7e2911e8c4c2c7a40782e0a95462fcd15b0ae1d63f2bdc5c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
