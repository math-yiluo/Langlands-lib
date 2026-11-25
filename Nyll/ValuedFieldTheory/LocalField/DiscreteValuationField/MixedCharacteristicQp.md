# A mixed-characteristic local field is a finite extension of ℚ_p

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicQp`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field `F` on a field `K` of characteristic zero (`[CharZero K]`), with residue characteristic `p`, the file finds a copy of `ℚ_p` inside `K` and proves that `K` is finite-dimensional over it. The file's docstring places this as the mixed-characteristic branch of the converse direction of the library's structure classification of local fields.

## Main definitions and results

- `qpadicClosureSubfield F`: the topological closure of the prime field `ℚ` in `K`, for the topology of the range-restricted valuation (`mrangeRestrictValued`, with value group `mrangeValueGroup F`). It is closed and complete.
- `ratCast_mrangeRestrict_valuation_isEquiv_padicValuation`: the valuation of `K`, restricted to `ℚ`, is equivalent to the `p`-adic valuation. Hence the embedding of `ℚ` with its `p`-adic uniformity into `K` is uniformly inducing (`ratCastWithValToK_isUniformInducing`).
- `qpadicNumbersEquivQpadicClosureSubfield : ℚ_p ≃+* qpadicClosureSubfield F`, extending the inclusion of `ℚ`.
- `qpadicNumbersAlgebra`: the resulting `Algebra ℚ_p K`, and `finiteDimensional_over_qpadicNumbers`: `K` is finite-dimensional over `ℚ_p` for it.
- `mixedCharacteristic_exists_qpadic_finiteExtension`: there are a prime `p` equal to the residue characteristic and an algebra structure of `K` over `ℚ_p` for which `K` is finite-dimensional.

## Proofs

The map from `ℚ_p` is the extension of `ℚ → K` to the completion (`UniformSpace.Completion.extensionHom`); uniform continuity of `ℚ → K` uses that powers of `p` tend to zero (`mrangeRestrict_exists_residueCharacteristic_pow_lt_unit`). The extension is uniformly inducing, hence a closed embedding, and has dense range, so it is onto the closure. Since `0 < ‖p‖ < 1`, the closure is a nontrivially normed field; finite dimension then follows from local compactness of `K` (`FiniteDimensional.of_locallyCompactSpace`) and is transported to `ℚ_p` by a rank comparison.

## Points to watch

- The topology, norms and the `ℚ_p`-algebra structure are not global instances: `qpadicNumbersAlgebra`, `qpadicClosureSubfield_nontriviallyNormedField` and `qpadicClosureSubfield_normedAlgebra` are definitions, introduced by `let` inside the statements.
- The final theorem is existential and does not record which algebra structure it uses; the canonical one is `qpadicNumbersAlgebra`, and `finiteDimensional_over_qpadicNumbers` is the statement about it.
- Equal characteristic is not treated here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/MixedCharacteristicQp.lean`: the Lean file is the source byte for byte (SHA-256 `01955ecfac6736776df0a868bac1ad0c57734542400f305a2623a503a5549d0d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
