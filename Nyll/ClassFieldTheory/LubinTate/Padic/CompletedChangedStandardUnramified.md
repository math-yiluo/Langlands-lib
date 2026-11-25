# The standard–changed compositum is unramified over the changed field

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let u be a unit of ℤ_p, D the changed-uniformizer fixed field and M the standard–changed compositum at level n, both finite extensions of ℚ_p inside the completed Lubin–Tate level E, with their spectral valuations. The file shows that M/D is unramified: the changed prime element, a uniformizer of E, is a uniformizer of both D and M.

## Main results

- `padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum`: the changed prime element `padicCompletedChangedUniformizerPrimeElement p u n` is a uniformizer of D, and its image in M is a uniformizer of M.
- `padicCompletedStandardChangedCompositum_ramificationIndex_eq_one`: the ramification index of M over D is 1.
- `padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension`: M is an unramified valued extension of D in the library's sense (`IsUnramifiedValuedExtension`, here verified through the ramification index of the maximal ideal).

## Proofs

The changed theta value is a uniformizer of E (imported). Since the valuations of D and M are, by uniqueness of extensions of the p-adic valuation to finite separable extensions, equivalent to the restriction of the valuation of E, an element of D or M that is a uniformizer of E is a uniformizer there (`isUniformizer_of_ambient_image_isUniformizer`). A common uniformizer gives ramification index 1.

## Watch for

- Each statement opens with `let` bindings fixing the spectral norm, valuation and local-field structures on D and M; the unramifiedness statement also binds the finiteness and separability of M over D; the results are about these structures.
- `IsUnramifiedValuedExtension` is the library's own notion; here it is established by showing that the ramification index of the maximal ideal is 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedStandardUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `0de72792148276b1b56a024c96019716bd8f1117a3ef5747ddd64960cbbb9067`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
