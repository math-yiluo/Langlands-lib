# A model of a number field in universe 0

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A number field is finite-dimensional over the countable field `ℚ`, hence countable, so it has a copy in the lowest universe. This file records this, for use where a construction needs number fields living in `Type`.

## Main results

- `ClassFieldTheory.numberField_small`: every number field `F`, in any universe, is `Small.{0}`.
- `ClassFieldTheory.numberField_shrink`: the copy `Shrink.{0} F`, with the field structure transported from `F`, is again a number field.

## Proof

Countability comes from Mathlib's countability of finite modules over a countable ring; the number-field structure is transported along the ring isomorphism between `F` and its shrunk copy.

## Points to watch

- `numberField_shrink` is a theorem whose statement first installs the `Small` instance from `numberField_small`; to use it, the same instance must be in scope.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/SmallModel.lean`: the Lean file is the source byte for byte (SHA-256 `b674824fc8e758afdb3a5d9a4ffcbfa11506eb88215c42be274a042046da8a48`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
