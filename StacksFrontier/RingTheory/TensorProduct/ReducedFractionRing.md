# Total rings of fractions after base change and reduction

Module `StacksFrontier.RingTheory.TensorProduct.ReducedFractionRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file identifies the total ring of fractions of the reduction of a tensor product using a localization of its factors. Here reduction means quotient by the nilradical.

- `nilradicalQuotientAlgebra` equips the reduction of a commutative algebra with an algebra structure over the reduction of its base. `isFractionRing_nilradicalQuotient` shows that if S is an Artinian localization of R at a submonoid of nonzerodivisors, then the reduction of S is the total ring of fractions of the reduction of R.
- `tensorProductFractionRingAlgebra` builds the algebra map from `O ⊗[A] B` to `F ⊗[K] L` from O → F and B → L. With the indicated scalar towers, `isLocalization_tensorProduct_fractionRing` identifies the latter tensor product as the localization of the former at images of nonzerodivisors of O. Here K and F are the localizations of A and O at their respective nonzerodivisors, and L localizes B at the images of the nonzerodivisors of A.
- `isFractionRing_nilradicalQuotient_tensorProduct` identifies the reduction of `F ⊗[K] L` as the total ring of fractions of the reduction of `O ⊗[A] B`. It assumes O is a domain, F is Artinian, B is flat over A, and L is finite as a K-module.

The proof pastes localization pushouts, then uses flatness to preserve the denominators as nonzerodivisors. Reduction commutes with localization, and finite base change makes the resulting ring Artinian, where every nonzerodivisor is a unit.

The fraction-ring theorem allows A to be any commutative ring and asks for finiteness of L over K. Both sides of its fraction-ring identification use reductions.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/TensorProduct/ReducedFractionRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
