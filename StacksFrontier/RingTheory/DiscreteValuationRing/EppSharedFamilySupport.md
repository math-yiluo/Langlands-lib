# One Galois residue extension for a finite family of roots

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFamilySupport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file constructs a finite weakly unramified extension of a discrete valuation ring whose residue field represents selected deep roots from a family of local rings. It also proves the field-theoretic construction that combines data from several extension fields.

- `exists_isGalois_splits_finset` puts a root with the specified minimal polynomial in one finite Galois extension of k for every member of a finite set of monic, separable, irreducible polynomials over k.
- `exists_isGalois_forall_family_minpoly_representatives` applies this to finite sets of separable integral elements in a finite family of extension fields of k. One extension, in the universe of k, contains an element with the same minimal polynomial as each selected element.
- `EppCondition.exists_isWeaklyUnramified_isGalois_residue_family_root_representatives` takes a discrete valuation ring R and finitely many local R-algebras Sᵢ with local structure maps and residue fields of exponential characteristic p. Given finite sets in their perfect cores and a depth N, it supplies one module-finite weakly unramified extension R₂ of R with Galois residue extension. For each selected element x it gives a root r in the corresponding residue field whose pᴺ-th power is x, and an element of the residue field of R₂ with the same minimal polynomial as r over the residue field of R.

Inverse Frobenius in each perfect core provides the roots. The proof takes the splitting field of the product of their distinct minimal polynomials, then lifts that finite Galois residue extension to a weakly unramified ring extension.

The hypothesis `h` assumes Epp’s condition for each R → Sᵢ and gives separability of the chosen roots over the base residue field. The conclusion matches minimal polynomials for the given finite sets at one depth.

The comments discuss Tag 09F8, clause (3) of Tag 09ET, and Tag 09F9 as context for the family construction.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFamilySupport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
