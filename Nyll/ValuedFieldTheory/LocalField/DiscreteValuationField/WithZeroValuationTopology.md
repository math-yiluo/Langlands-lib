# Completeness for the topology of a `ℤᵐ⁰`-valued complete discrete valuation

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.WithZeroValuationTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation `v` on a field `K` with values in `ℤᵐ⁰` that is complete and discrete (`Valuation.IsCompleteDiscrete`, a library class), the file shows that `K` is complete for the topology of `Valued.mk' v`, when the residue field is finite.

- `WithZeroValuationTopology.completeDVF v`: `v` packaged as a `CompleteDVF K` with value group `ℤᵐ⁰`.
- `valuedMk_uniformSpace_eq_mrangeRestrict`: the uniform structure of `Valued.mk' v` equals that of the valuation restricted to its range.
- `completeSpace_ofWithZeroValuation`: if the residue field of `v` is finite, `K` is complete for `Valued.mk' v`.

The proof notes that `v` and its range restriction are equivalent valuations, so they define the same uniform structure, and then uses completeness of the range-restricted normed field with finite residue field, proved in the file on range-restricted topology.

Finiteness of the residue field is a hypothesis of the completeness statement: completeness is obtained here from properness, which needs it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/WithZeroValuationTopology.lean`: the Lean file is the source byte for byte (SHA-256 `47497e89890cb8ccc7540298f416476edeb8efdbf1dafdfe126f9f6b93b84b96`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
