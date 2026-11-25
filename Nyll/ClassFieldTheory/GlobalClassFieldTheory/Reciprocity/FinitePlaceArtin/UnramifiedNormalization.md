# Unramified normalization of the finite-place Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.UnramifiedNormalization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and v a finite place of K. When the chosen local extension at v is unramified, the file computes the local Artin image of the chosen local element of order one.

- `chosenFinitePlaceLocalArithmeticFrobenius v hunram`: the arithmetic Frobenius (`arithmeticFrobeniusOfUnramifiedValuation`) of the chosen localized completion of L over the chosen completion of K, given `hunram : ChosenFinitePlaceIsUnramified v`.
- `chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified`: `finitePlaceLocalArtinMonoidHom` at the chosen extension sends `FiniteIdeleGroup.chosenLocalOrderSection v 1` to the inverse of that Frobenius.

The proof uses that the Artin input of this element has normalized valuation −1 in the construction (`finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap`). Its inverse then has valuation 1, so the local theorem `abelianLocalArtinMap_uniformizer` sends it to arithmetic Frobenius; inverting gives the claim.

## Points to watch

- The finite-place Artin map is geometrically normalized: at an unramified place the chosen element of order one goes to inverse arithmetic Frobenius, not to arithmetic Frobenius.
- Unramifiedness is the library's predicate `ChosenFinitePlaceIsUnramified` on the chosen completions, used as the instance `IsUnramifiedValuedExtension`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/UnramifiedNormalization.lean`: the Lean file is the source byte for byte (SHA-256 `538e51d400f1beb6a7cb67f6bf2202d4b3892f83877f82b154532ed8fa6f09da`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
