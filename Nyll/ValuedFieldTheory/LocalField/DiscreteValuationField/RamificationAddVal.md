# Additive valuations in an extension scale by the ramification index

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `base` and `target` be fields K and L with chosen complete discrete valuations (the library's `CompleteDVF`), L an algebra over K, and the valuation of L extending that of K (`HasExtension`). The file shows that the normalized additive valuation of O_L, restricted to O_K, is e times that of O_K, where e is the library's ramification index.

- `addVal_integerMap_eq_ramificationIndex_nsmul`: for every a ∈ O_K, v_L(a) = e · v_K(a), with `IsDiscreteValuationRing.addVal` (values in ℕ∞, so a = 0 gives ⊤ on both sides) and `integerMap` the map O_K → O_L.
- `addVal_integerMap_eq_ramificationIndex_of_irreducible`: a uniformizer of O_K has valuation e in O_L.
- `ramificationIndex_eq_one_of_integerMap_uniformizer`: if a uniformizer of K stays a uniformizer of L, then e = 1.

The proof writes a = unit · π^m and uses the ideal identity 𝔪_K O_L = 𝔪_L^e from the companion file on ramification ideals, which shows that π maps to an associate of ϖ^e for a uniformizer ϖ of L. The same identity gives e ≠ 0, needed for the case a = 0.

The module docstring speaks of finite extensions, but no finiteness of L over K is assumed in the statements; e is the library's ideal-theoretic ramification index of 𝔪_L over 𝔪_K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean`: the Lean file is the source byte for byte (SHA-256 `6ea63e1c4338ae773d9baa28d3f20fe9d58333b912c03da4b950a15465cd1024`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
