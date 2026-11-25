# A stalk algebra over the local ring of an affine base

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.StalkBaseAlgebra`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For f : X ⟶ Spec R and x ∈ X, the local ring of X at x is an algebra over R localized at the prime p of f(x).

`localizationAtPrimeToStalk` composes the canonical identification of R_p with the base stalk and the stalk map of f. It is a local homomorphism and defines `stalkAlgebraOfSpecHom`. If f is flat, `flat_localizationAtPrimeToStalk` gives flatness and `faithfullyFlat_stalkAlgebraOfSpecHom` uses locality to give faithful flatness. The resulting faithful scalar action, recorded by `faithfulSMul_stalkAlgebraOfSpecHom`, gives injectivity.

`isExtension_stalkAlgebraOfSpecHom` uses locality and injectivity to obtain an extension of discrete valuation rings in the sense of Tag 09E4. It requires flatness of f and explicit domain and discrete valuation ring instances for both local rings.

The definitions take primality of the ideal at f(x) as a typeclass argument.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Affine/StalkBaseAlgebra.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.algebraMap_stalkAlgebraOfSpecHom`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
