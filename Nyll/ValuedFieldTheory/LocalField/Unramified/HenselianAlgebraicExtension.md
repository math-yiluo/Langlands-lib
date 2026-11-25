# Algebraic extensions of a Henselian valued field are Henselian

Module `Nyll.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that Henselianity passes to algebraic extensions, for valuations given as exponential valuations (`ExponentialValuation`, values in `ℝ ∪ {∞}`). Henselianity is the library's `HenselianValuationByFactorization`, a Hensel factorization property of the valuation ring.

- `exponentialValuation_hasUniqueAlgebraicValuationSubringExtensions`: if `v` on `K` is Henselian, its valuation ring extends uniquely to every algebraic extension of `K` in the same universe.
- `henselianValuation_of_algebraic_extension`: if `L / K` is algebraic, `w` on `L` restricts to `v` on `K`, and `v` is Henselian, then `w` is Henselian. `K` and `L` may lie in different universes.

Both proofs pass to the associated nonarchimedean absolute value (base `e`), which has the same valuation ring. The second turns the factorization property into a `HenselianRing` structure, transfers it to the valuation ring of `w` by an earlier result on algebraic extensions, and converts back.

## Watch for

The first result requires `L` in the universe of `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Unramified/HenselianAlgebraicExtension.lean`: the Lean file is the source byte for byte (SHA-256 `ddba265846022077268214328e21bee51bc2b0c54b6a6bef6081bef63958ee73`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
