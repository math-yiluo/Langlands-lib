# Valuation-ring actions and Galois restriction

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Consider a tower K ⊆ L ⊆ M of fields with L/K normal, with discrete valuations `base`, `middle` and `target` on K, L and M (the library's `DVF` structures), each extending the ones below it. When the valuation of K extends uniquely to L and to M, Gal(L/K) acts on the valuation ring of L and Gal(M/K) acts on that of M. The file shows that the two actions are compatible.

`valuationSubringAutOfUniqueExtension_integerMap_restrictNormal`: for σ in Gal(M/K) and a in the valuation ring of L, applying σ to the image of a in the valuation ring of M (via `integerMap`) gives the image of the restriction σ|_L applied to a.

The proof reduces to Mathlib's `AlgEquiv.restrictNormal_commutes`.

Watch for: the two unique-extension hypotheses, `hmiddle` for L over K and `htarget` for M over K, are explicit arguments of type `DVF.HasUniqueValuationExtension`. The three compatibility conditions `HasExtension` are assumed separately.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `195a368ffa04860a99a88bd03cfe81a2deea866f93199fa283c442ef5b70ad6b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
