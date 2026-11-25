# Adjoining roots in extensions of discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AdjoinRootExtensions`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

These lemmas construct finite separable extensions in which a uniformizer acquires a root. They also identify the field factors of reduced tensor products and compare their integral closures.

- `IsDiscreteValuationRing.exists_finite_separable_extension_uniformizer_pow_eq` starts with an injective local extension of discrete valuation rings A → R, the fraction field K of R, and a uniformizer π of A. If n is positive, invertible in R and divides the ramification index, there is a finite separable extension E/K with an n-th root of the image of π. The integral closure of R in E is finite étale over R.
- `IsDiscreteValuationRing.exists_tensorProduct_quotNilradical_equiv_pi_fields` identifies the reduction of L ⊗ₖ K₁ with a nonempty finite product of fields finite over L, assuming K₁/K is finite. The equivalence respects the two field inclusions. `IsDiscreteValuationRing.exists_surjective_tensorProduct_projection` gives the compatible surjection onto each such factor.
- `IsDiscreteValuationRing.exists_tensorProduct_adjoinRoot_equiv` identifies base change of an `AdjoinRoot` algebra with adjoining a root of the mapped polynomial, matching the root generators. `IsDiscreteValuationRing.formallyEtale_integralClosure_of_tensorProduct_adjoinRoot_factor` gives formal étaleness of the integral closure of R in a field factor of the base change to L of the algebra adjoining an n-th root of a. It assumes R integrally closed in L, n positive and invertible in R, and the image of a in L equal to cⁿ times a unit from R, with c a unit of L.
- `IsDiscreteValuationRing.formallySmoothNAdic_of_ramificationIndex_eq` transfers maximal-ideal-adic formal smoothness from B → D to C → D in compatible discrete valuation ring towers over A. It requires equal ramification indices for A → B and A → C, the library’s `Algebra.StacksIsSeparableExtension` for the residue extension of A → B and a surjective residue map for A → C. That notion asks every finitely generated intermediate field to be separably generated, so it does not force the residue extension to be algebraic; `IsDiscreteValuationRing.isSeparableExtension_of_ringChar_eq_zero` proves it for every extension of a field of characteristic zero.

The root construction writes the image of π as a unit times a power of a uniformizer of R, then adjoins a root of the unit using a monic separable polynomial. The tensor decomposition uses the structure theorem for reduced Artinian rings. Auxiliary lemmas pass integral closures through finite products and construct maps between normalizations and their localizations.

The field witnessing the uniformizer root lives in the same universe as K.

Stacks Project, Tag 0BRM.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/AdjoinRootExtensions.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 37 declarations of the source file 33 are kept. The 4 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.etale_integralClosure_of_adjoinRoot_equiv`, `IsDiscreteValuationRing.formallySmoothNAdic_of_formallySmooth_square`, `IsDiscreteValuationRing.formallySmooth_integralClosure_of_algEquiv_pi`, `IsDiscreteValuationRing.formallySmooth_integralClosure_of_surjective`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
