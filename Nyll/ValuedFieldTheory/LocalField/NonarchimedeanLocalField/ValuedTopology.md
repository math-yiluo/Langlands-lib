# The topology of a valued field is valuative

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

When a valued field is given a `ValuativeRel` through its valuation, one must know that its topology is the topology of that relation. This file proves it.

## Main result

- `isValuativeTopology_of_valued_ofValuation`: let `F` be a field with `Valued F Γ`, where `Γ` is a linearly ordered commutative group with zero that is `MulArchimedean`, and suppose the valuation `Valued.v` is nontrivial. Then, for the valuative relation `ValuativeRel.ofValuation Valued.v`, the topology of `F` satisfies `IsValuativeTopology F`.

The proof checks neighbourhoods of zero with `IsValuativeTopology.of_zero`: a ball `{v z < δ}` of `F` and a ball of `F` with radius in the value group of the relation correspond through the order isomorphism between that value group and the image of `v` (`ValuativeRel.ValueGroupWithZero.orderMonoidIso`).

## Watch for

The hypothesis `MulArchimedean Γ` is assumed; the statement is made for the relation induced by the valuation, introduced by a `letI` inside the statement, so it applies only when that is the `ValuativeRel` instance in use.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuedTopology.lean`: the Lean file is the source byte for byte (SHA-256 `68a3773bcf34dfaef07f11d243f5227a9479031d226d7b117e36ab5deb16aac8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
