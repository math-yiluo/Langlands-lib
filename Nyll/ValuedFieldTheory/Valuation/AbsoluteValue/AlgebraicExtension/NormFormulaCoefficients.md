# Coefficient bounds for irreducible polynomials from Hensel factorization

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nonarchimedean absolute value on a field `K` whose valuation ring `𝒪_v` satisfies a factorization form of Hensel's lemma. For an irreducible polynomial over `K`, this file bounds every coefficient by the larger of the values of the constant and the leading coefficient. This is a step towards the norm formula for extending `v`.

## Main results

All results assume that `v` is nonarchimedean (the library's `NonarchimedeanAbsoluteValue`) and that `𝒪_v` satisfies `HenselFactorizationProperty`.

- `normFormula_coeff_abs_le_endpoint_max_of_irreducible_of_henselFactorization`: for `f` irreducible, `v(fᵢ) ≤ max(v(f₀), v(lead f))` for every `i`.
- `normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization`: if `f` is monic and irreducible and `v(f₀) ≤ 1`, then every coefficient has value at most `1`.

Helper results lead up to these:
- a polynomial over `𝒪_v` whose reduction is `X^r · q̄`, with `0 < r < deg`, `q̄` coprime to `X^r` and `q̄(0) ≠ 0`, has a non-irreducible image over `K`;
- the same conclusion for `f` scaled by the inverse of a coefficient of maximal value, when both end coefficients have strictly smaller value;
- the resulting bound on that maximal value.

## Proof

Suppose the maximal coefficient value `m > 0` exceeds both end values. Divide `f` by a coefficient of value `m`. The reduction of the result then splits as `X^r` times a coprime factor. The factorization hypothesis lifts this splitting, which contradicts irreducibility. The normalization lemmas come from the imported file on lifting irreducible polynomials.

## Points to watch

`HenselFactorizationProperty` is the library's own predicate. It stands for Hensel's lemma and is carried as a hypothesis. The file assumes neither completeness nor separatedness and does not derive the property from them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/NormFormulaCoefficients.lean`: the Lean file is the source byte for byte (SHA-256 `a46675f8977b043738ed8aca96643c2cc06f85b14c547b04bd411a554c05f579`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
