# A nonarchimedean local field is universe-small

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Small`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The single theorem `nonarchimedeanLocalField_small` says that a nonarchimedean local field `K` in any universe is `Small.{0}`: its carrier is in bijection with a type in `Type 0`. This allows the library to replace `K` by a copy in universe `0`.

The proof uses the complete discretely valued field structure `localCompleteDVF K` from an imported file. Its valuation ring `O` is complete and separated for the adic topology of its maximal ideal `I`, so `x ↦ (x mod I^n)ₙ` embeds `O` into the product of the quotients `O/I^n`, which the library knows to be small (they are finite since the residue field is finite). Since `K` is the fraction field of `O`, the map `(a, b) ↦ a/b` from `O × O` onto `K` makes `K` small.

Only smallness is proved; the module comment stresses that no countability of `K` is asserted.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean`: the Lean file is the source byte for byte (SHA-256 `62c8752dc832f0d0a5f6acd823fe8d70e5e8e8d1231d43c28110d3c54def3384`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
