# Topological decomposition of ℤ_pˣ

Module `Nyll.ValuedFieldTheory.LocalField.Padic.UnitDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file specializes the library's structure theorem for units of a mixed-characteristic local field to `ℚ_[p]`, presented through its discrete valuation `padicDVRValuation p`. The outcome is an isomorphism of topological groups between `ℤ_[p]ˣ` and a finite group times the additive group of `ℤ_[p]`.

## Main definitions

- `padicUnitDecomposition p : padicUnitFiniteFactor p × Multiplicative ℤ_[p] ≃ₜ* ℤ_[p]ˣ`: the decomposition. It combines the splitting of units of the valuation ring into roots of unity of the residue field times first principal units, with the structure theorem for first principal units, `U¹ ≃ ℤ/p^a × ℤ_p^d`.
- `padicUnitFiniteFactor p`: the finite factor `ℤ/(q − 1) × ℤ/p^a`, where `q` is the cardinality of the residue field and `a` is the exponent returned by the structure theorem; `padicUnitFiniteFactor_finite` shows it is finite.
- `padicPrincipalData p`: the structure data for `U¹`, transported from the topology defined by the valuation to the standard topology of `ℚ_[p]` (`padicPrincipalDataDirect`, `padicPrincipalMulData` are the version before transport and the bare group isomorphism).
- `padicFreeContinuousAddEquiv p`: the free factor, `d` copies of `ℤ_[r]` with `r` the residue characteristic, is `ℤ_[p]`, once `r = p` and `d = 1`.
- `padicIntValuationSubringContinuousMulEquiv p`: `ℤ_[p]` and the valuation subring of `padicDVRValuation p` as topological monoids; `padicResidueEquivZMod p`: the residue field is `ℤ/p`.
- Generic helpers on continuous multiplicative equivalences: products, associativity, passing from additive to multiplicative.

## Main results

- `padicDVRValuation_surjective`: the valuation maps onto `ℤᵐ⁰`.
- `padic_residueCharacteristic_eq`: the residue characteristic is `p`.
- `padicDVRValued_uniformSpace_eq_standard`: the uniform structure from the valuation is the standard one on `ℚ_[p]`, because the valuation and the norm have the same unit ball.
- `padic_finrank_eq_one`: `ℚ_[p]` has degree 1 over the copy of `ℚ_p` built from the residue characteristic; the embedding has closed and dense image.
- `padicPrincipalUnitDirectTopology_eq_standard`: the two topologies on `U¹` agree.

The decomposition is assembled from these by composing continuous isomorphisms; the final map is continuous by construction and becomes a homeomorphism because its source is compact and its target Hausdorff.

## Watch for

- The decomposition is a chosen one and is not canonical; the exponent `a` of the finite `p`-part is left as whatever the structure theorem chose, and the file does not compute it.
- The finite factor is written as `ℤ/(q − 1)` with `q` the number of elements of the residue field and the second factor with the residue characteristic, not with `p − 1` and `p`; the identification with `ℤ/p` of the residue field is proved, but not substituted into the type.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Padic/UnitDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `57b2a9d638e8d2f40956d962d331a3894481caf426ecdfa061129344d77a6367`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
