# Unique extension of valuations for Henselian discretely valued fields

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianValuationExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For Henselian discretely valued fields `K` and `L` (the library's `HenselianDVF`) with `L` a `K`-algebra, the file defines a predicate saying that every extension to `L` of the valuation of `K` is equivalent to the valuation of `L`, and gives reformulations in terms of valuation subrings. Nothing here proves that uniqueness holds.

## Definitions and results

- `HasUniqueValuationExtension base target`: every valuation `v'` of `L` extending the valuation of `K`, with values in a linearly ordered commutative group with zero of a fixed universe `y`, is equivalent (Mathlib's `Valuation.IsEquiv`) to the valuation of `target`.
- `valuation_isEquiv_iff_valuationSubring_eq`, `valuation_isEquiv_iff_mem_valuationSubring` and one-directional forms: the target valuation is equivalent to `v'` exactly when the two valuation subrings coincide, equivalently have the same elements.
- `hasUniqueValuationExtension_iff_forall_valuationSubring_eq` and `hasUniqueValuationExtension_iff_forall_mem_valuationSubring`: the predicate holds exactly when the target valuation subring equals that of every extension `v'`, or has the same elements; `hasUniqueValuationExtension_of_forall_valuationSubring_eq` and `valuationSubring_eq_of_hasUniqueValuationExtension` are the two directions.

All of these are direct consequences of Mathlib's `Valuation.isEquiv_iff_valuationSubring`.

## Caveats

- The predicate is the library's own; uniqueness is meant up to equivalence and quantifies only over value groups in the single universe `y`.
- The predicate does not itself assert that the valuation of `target` extends that of `K`.
- No finiteness or algebraicity of `L/K` is assumed in this file, and the `base` argument of the first five lemmas is not used in their statements.
- It is the analogue, without completeness, of the complete-DVF predicate `ValuedExtension.HasUniqueValuationExtension`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianValuationExtension.lean`: the Lean file is the source byte for byte (SHA-256 `f7430d7f4a21162d9bca662de70fb264622ba04e964dfb88727095daa41aaa68`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
