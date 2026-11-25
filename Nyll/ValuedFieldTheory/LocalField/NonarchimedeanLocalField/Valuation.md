# The normalized integer valuation of a nonarchimedean local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file characterizes the valuation ring by `ValuativeRel.valuation K x ≤ 1` and, for a nonarchimedean local field `K`, packages the normalized ℤ-valued valuation on `Kˣ` as a surjective homomorphism with a uniformizer.

- `valuation_integer_membership`: `x ∈ 𝒪[K]` iff the valuation of `x` is at most one; any field with a `ValuativeRel`.
- `multiplicativeIntegerValuation`: the normalized valuation `IsNonarchimedeanLocalField.v K` on `Kˣ`, as a `MultiplicativeIntegerValuation Kˣ`; `multiplicativeIntegerValuation_val` unfolds it.
- `multiplicativeIntegerValuation_surjective`: it maps `Kˣ` onto ℤ, by surjectivity of `v`.
- `multiplicativeIntegerValuation_exists_uniformizer`: some unit `ϖ` is a uniformizer for it.

## Watch for

`MultiplicativeIntegerValuation` is the library's structure (a homomorphism to ℤ), not a Mathlib valuation, and "uniformizer" is meant in its sense. Whether such `ϖ` is a uniformizer of `𝒪[K]` or its inverse depends on the sign convention of `v`, fixed elsewhere in the library.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Valuation.lean`: the Lean file is the source byte for byte (SHA-256 `8a377ec4a285271c1aa9ca33eaffb81bb6d002b4f154ccd8b797fe6cdb077bca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
