# The restricted valuation ring of a fixed field

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldValuationRing`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of discretely valued fields, the valuation of `L` extending that of `K`, and `H` a subgroup of `Gal(L/K)` with fixed field `M = L^H`. The file restricts the valuation ring `O_L` to `M`, giving `O_M = O_L ∩ M`. When `L/K` is finite Galois and the valuation extends uniquely, `O_M` is the integral closure of `O_K` in `M`; for normal `H` it is also a discrete valuation ring, and `Gal(M/K)` acts on it. The file's comment notes that no completeness or Henselian hypothesis is used.

## Main definitions and results

- `fixedFieldDVF H`: the fixed field `L^H`. `fixedFieldValuationSubringDVF H`: the valuation subring `O_L ∩ M` of `M`.
- `fixedFieldValuationSubringDVFToTarget` (injective), `baseToFixedFieldValuationSubringDVF`, `fixedFieldValuationSubringDVFToTargetAlgHom`: the inclusions `O_K → O_M → O_L`. An instance says that the valuation of `O_M` extends the base valuation.
- With `L/K` finite Galois and unique extension `huniq`:
  - `fixedFieldValuationSubringDVF_isIntegral` and `fixedFieldValuationSubringDVF_isIntegralClosure`: `O_M` is integral over `O_K` and is the integral closure of `O_K` in `M`;
  - for normal `H`: `fixedFieldValuationSubringDVF_moduleFinite` (`O_M` is a finite `O_K`-module) and `fixedFieldValuationSubringDVF_isDiscreteValuationRing` (`O_M` is a discrete valuation ring).
- Galois action, for normal `H`:
  - `fixedFieldValuationSubringLiftedAutDVF huniq H σ`: for `σ ∈ Gal(L/K)`, its image in `Gal(M/K) ≅ Gal(L/K)/H` restricted to `O_M`; `fixedFieldValuationSubringDVFToTarget_aut_apply` shows it is compatible with the action of `σ` on `O_L`;
  - `fixedFieldDVF_aut_mem_valuationSubring_iff`: every `q ∈ Gal(M/K)` preserves `O_M`;
  - `fixedFieldValuationSubringAutDVF huniq H q`: the resulting ring automorphism of `O_M`, multiplicative in `q`, and equal to the lifted automorphism for any lift `σ` of `q`.

## Proofs

Integrality passes from `O_L`, which is the integral closure of `O_K` in `L` under unique extension. Finiteness follows from `O_K` being Noetherian. `O_M` is then a Noetherian valuation ring that is not a field, hence a discrete valuation ring. Preservation of `O_M` by `q` uses a lift of `q` to `Gal(L/K)`, which preserves `O_L` by uniqueness of the extension.

## Points to watch

- Uniqueness of the valuation extension is the explicit hypothesis `huniq`.
- Finiteness, the discrete valuation ring property and the Galois action are stated for normal `H` only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FixedFieldValuationRing.lean`: the Lean file is the source byte for byte (SHA-256 `dfc2c1040a018454645fcdfa13f4129a13b2212d77292674f4a4b785fc8ee675`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
