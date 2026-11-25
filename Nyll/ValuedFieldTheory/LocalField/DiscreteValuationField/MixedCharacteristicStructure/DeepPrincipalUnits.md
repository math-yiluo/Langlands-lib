# Deep principal units in mixed characteristic are ℤ_p^d

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.DeepPrincipalUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field of characteristic zero, complete for a discrete valuation `v : K → ℤᵐ⁰` with finite residue field of characteristic `p`, and let `F = ofWithZeroValuation v` be the associated local field. The file shows that for `v` surjective and `n > e/(p − 1)`, with `e` the ramification index, the higher principal units `U^n` are isomorphic to `ℤ_p^d`, `d = [K : ℚ_p]`, both as `ℤ_p`-modules and as topological spaces, by composing a logarithm `U^n → m^n` with integral-basis coordinates on `m^n`.

## Main definitions and results

- `MixedWithZeroValuationContext v`: a class bundling the library's integral `ℚ_p`/`ℤ_p`-algebra context for `F` with a valued-field structure on `K` (a field `valued : Valued K ℤᵐ⁰` that the class does not tie to `v`); `mixedWithZeroValuationContext v` is the canonical value, with `Valued.mk' v`.
- Continuity for the topology of `v`: the embedding `ℚ_p → K` (`continuous_qpadicNumbersAlgebra_ofWithZeroValuation`), the map `ℤ_p → O_K`, and the `ℤ_p`-actions on `O_K`, on `m^n`, on `U^1` and on every `U^r` with `r ≥ 1`.
- `mixed_maximalIdealPowHomeomorphPi_ofWithZeroValuation`: `m^n ≃ₜ ℤ_p^d`, the coordinates of a chosen `ℤ_p`-basis.
- `mixed_deepLogContinuousAddEquiv`: for `e/(p − 1) < n` and `v` surjective, `U^n ≃ₜ+ m^n` (`U^n` written additively), the logarithm side of the imported equivalence `MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv`.
- `mixed_deepLogLinearEquiv`: the same map as a `ℤ_p`-linear equivalence; `mixed_deepPrincipalUnit_moduleFinite`: `U^n` is a finitely generated `ℤ_p`-module.
- `mixed_deepPrincipalUnitLinearEquivPi : U^n ≃ₗ[ℤ_p] ℤ_p^d` and `mixed_deepPrincipalUnitHomeomorphPi : U^n ≃ₜ ℤ_p^d`.

## Proofs

Continuity of `ℚ_p → K` comes from the isomorphism of `ℚ_p` with the closure of `ℚ` in `K` and the equality of the uniformities of `v` and of its range restriction. Linearity of the logarithm over `ℤ_p` follows from additivity and continuity (`padicLinearEquivOfContinuousAddEquiv`). The coordinate map is a homeomorphism because its inverse `x ↦ Σ x_i b_i` is continuous and closed.

## Points to watch

- `mixed_deepPrincipalUnitHomeomorphPi` is typed only as a homeomorphism; the group structure is recorded separately by `mixed_deepPrincipalUnitLinearEquivPi`.
- The coordinates depend on a basis chosen by `Module.finBasisOfFinrankEq`, and the logarithm is taken from an imported equivalence whose name marks it as chosen.
- Everything is stated for the local field `ofWithZeroValuation v` built from the `ℤᵐ⁰`-valued valuation `v`, in `LocalField.{u, 0}`. Surjectivity of `v` (`hv`) is a hypothesis only of the logarithm and of the results built on it, not of the continuity statements or of `mixed_maximalIdealPowHomeomorphPi_ofWithZeroValuation`. The context, the valued structure and the `ℤ_p`-module structures are introduced by `let`, not as global instances. `mixedWithZeroValuationContext` is a definition, not an instance.
- `mixed_one_le_of_log_level` records that the depth condition forces `n ≥ 1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/MixedCharacteristicStructure/DeepPrincipalUnits.lean`: the Lean file is the source byte for byte (SHA-256 `a5f33d36bbd6b94eb3450625d0faebc8ff8ad6590ce54b04bb5e23f2c89f4e0e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
