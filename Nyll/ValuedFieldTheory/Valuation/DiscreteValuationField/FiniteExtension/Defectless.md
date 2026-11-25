# A finite extension of valuation rings has no defect

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For discretely valued fields `base` on `K` and `target` on `L` (the library's `DVF`) with the valuation of `target` extending that of `base`, the file proves `[L : K] = e · f` as soon as the valuation ring `O_L` is a finite `O_K`-module. Neither completeness nor Henselianity is used.

## Main result

- `isDefectless_of_moduleFinite`: if `O_L` is a finite `O_K`-module (and the scalar tower `O_K → O_L → L` is compatible), then `IsDefectless base target`, that is, `[L : K]` equals the ramification index times the residue degree.

## Proof

Since `O_L` is local, its maximal ideal is the only prime above `𝔪_K`. Mathlib's formula `∑ e_P f_P = rank` over the primes `P` above `𝔪_K` then has a single term, and the rank of `O_L` over `O_K` is `[L : K]` because `L` and `K` are the fraction fields of `O_L` and `O_K`.

## Points to watch

Finiteness of `O_L` over `O_K` is a hypothesis here; the file does not show when it holds.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Defectless.lean`: the Lean file is the source byte for byte (SHA-256 `683b0fa0d4b0a05071a37037bedffece7918d6f3b968fb199d436902dc02f8b0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
