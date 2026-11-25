# Value group of the local base valuation

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K`, the normalized valuation `Kˣ → ℤ` is moved to the group of Galois-fixed units of `SeparableClosure K` and embedded in `ZHat`. The file shows that its image is exactly the integers inside `ZHat` and that the quotient of the value group by its `n`-multiples is `ZMod n`, the conditions on the value group asked of a Henselian valuation in the class formation.

## Main definitions and results

- `baseFieldUnitsEquiv`: `Kˣ` is isomorphic to the units of `SeparableClosure K` fixed by the base subgroup; `baseFieldUnitsEquiv_val` says it is the algebra map.
- `localBaseValuation`: the normalized valuation, written on these fixed units, with values in `ZHat`.
- `localBaseValuation_range`: its range is the image of `ℤ` in `ZHat`; `intToProCInteger_mem_localBaseValuation_range` restates that every integer occurs.
- `localValueGroupReduction`, with `localValueGroupReduction_surjective` and `localValueGroupReduction_ker`: reduction modulo `n > 0` on the value group is onto `ZMod n` with kernel its `n`-multiples.
- `localValueGroupQuotientEquivZMod`: the quotient by `n`-multiples is isomorphic to `ZMod n`.
- `localCanonicalValueQuotientMap_bijective`: the class formation's canonical map from this quotient to `ZMod n` is bijective.

Surjectivity of the normalized valuation on `Kˣ` gives the range; the kernel computation reduces to divisibility in `ℤ`.

The field `K` is taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean`: the Lean file is the source byte for byte (SHA-256 `68d81075a4a6a733d39aac8bba4dad1e4263bc11bdd15d50d8914a8c2d52556d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
