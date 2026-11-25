# Completion data for integral local induction

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `vK` an absolute value on `K` and `w` an extension of `vK` to `L` (`AbsoluteValueExtension vK L`). The file fixes, in the namespace `LocalInductionInternal`, the algebra and valuation structures on the completions at `vK` and `w` that later files on integral local induction all use, so that they agree with one another.

## Main declarations

All definitions are `@[reducible]` defs, not instances.

- `extensionCompletionAlgebra`, `extensionCompletionSMul`: the `K`-algebra structure on the completion `w.1.Completion` of `L`, and its scalar action.
- `completionAlgebra`: the structure of a `vK.Completion`-algebra on `w.1.Completion`.
- `baseValued`, `baseValuativeRel`: the `ℝ≥0`-valued structure and the valuative relation on `vK.Completion`, for `vK` nonarchimedean.
- `localizedValued`, `localizedValuativeRel`: the same on `LocalizedCompletion vK w`.
- `integerAlgebra`: `LocalizedCompletion vK w` as an algebra over the valuation ring `𝒪[vK.Completion]`, by restriction of scalars to the subring.
- `valuationHasExtension` (theorem): the valuation of `LocalizedCompletion vK w` extends that of `vK.Completion`.
- `isIntegralClosure` (theorem): for `vK` nontrivial and nonarchimedean, the valuation ring of `LocalizedCompletion vK w` is the integral closure of `𝒪[vK.Completion]` in it.

The two theorems are taken from `localizedCompletionValuationHasExtension` and `localizedCompletionIsIntegralClosureWithExtension`.

## Points to watch

- The valuative relations, `integerAlgebra` and the two theorems are stated under `let`-bound copies of the preceding structures; later files must use these same choices for the statements to apply.
- `valuationHasExtension` holds without the number-field, finiteness and Galois hypotheses; `isIntegralClosure` keeps finite dimensionality of `L/K` but drops the number-field and Galois hypotheses.
- All declarations take `K` and `L` in `Type`, the lowest universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/LocalInduction/Spine.lean`: the Lean file is the source byte for byte (SHA-256 `89f73799b0e77ca1b767c1e4e477ec06fbfe3d65609e8dbbcb89f130c06bc901`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
