# Restricting a valuation ring to a finite separable subextension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueValuationComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over a complete discretely valued field, the valuation extends uniquely to a finite separable extension. This file uses that to compare a valuation ring restricted from an ambient field with any other extension valuation ring on a finite intermediate field, as needed before comparing residue degrees in finite local reciprocity.

`ValuationSubring.restrictIntermediateField_eq_of_finite_separable`: let `base : CompleteDVF K` be a complete discrete valuation on `K`, `A` a valuation ring of an extension field `Omega` whose valuation extends `base`, and `E` an intermediate field, finite and separable over `K`. If `C` is any valuation ring of `E` whose valuation extends `base`, then the restriction of `A` to `E` equals `C`.

Proof: the restriction of `A` also extends `base` (`restrictIntermediateField_hasExtension`); both it and `C` equal the valuation ring of a standard extension (`exists_integralClosure_standard_fundamental_identity`) by `target_valuationSubring_eq_of_finite_separable`.

`CompleteDVF` is the library's own structure. Although the header speaks of an algebraic ambient field, the statement assumes nothing about `Omega` beyond the extension of valuations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean`: the Lean file is the source byte for byte (SHA-256 `62d86ca80ce006b368ce56ffe816023f1b372fa446bcdf4dfc5ab5d72bb82c98`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
