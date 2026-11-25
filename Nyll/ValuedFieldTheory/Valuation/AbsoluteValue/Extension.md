# Extension of an absolute value along an algebra map

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Extension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines one predicate, used throughout the library's treatment of absolute values on field extensions.

- `AbsoluteValue.Extends v w`: for a field extension `L/K` with real-valued absolute values `v` on `K` and `w` on `L`, the statement that `w (algebraMap K L x) = v x` for every `x ∈ K`.

`Extends` asks for equality of values. Equivalence of absolute values is not enough, so a power `w^s` of an extension of `v` is in general not an extension of `v`. The predicate is the library's own, and it is stated only for absolute values with values in `ℝ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Extension.lean`: the Lean file is the source byte for byte (SHA-256 `758b10f0cf28eaf5be57a72f4d6cdaed549e964bb5fb6f2c4440dd1556bdd355`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
