# The exact sequence of inertia, decomposition and residue automorphisms

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a Galois extension, possibly infinite, and A a valuation subring of L, with the library's decomposition group D and inertia group I. Write λ for the residue field of A and κ for the residue field of the decomposition field Z, the fixed field of D. The file proves that λ/κ is normal and that reduction gives an exact sequence 1 → I → D → Aut_κ(λ) → 1.

## Definitions

- `decompositionFixedSubring K A`: the subring A^D of elements fixed by D. Its ideal `decompositionFixedMaximalIdeal` is the contraction of the maximal ideal of A, and `decompositionResidueField K A` is the quotient, which serves as κ. `selectedResidueField A` is λ.
- `decompositionFieldValuationSubring K A`: the valuation ring A ∩ Z of Z. `decompositionFieldValuationSubringEquivFixedSubring` identifies it with A^D, which makes A^D a local ring.
- `decompositionFieldResidueEquiv`: the residue field of Z is isomorphic to κ, and `decompositionFieldResidueMapToSelected` is the induced embedding into λ.
- `decompositionGroupResidueAction K A`: the homomorphism from D to the κ-automorphisms of λ given by reduction.
- `decompositionQuotientEquivResidueGalois`: the isomorphism D/I ≅ Aut_κ(λ).

## Results

- `decompositionFixedMaximalIdeal_eq_maximalIdeal`: the contracted ideal is the maximal ideal of A^D.
- `decompositionGroupResidueAction_ker`: the kernel of the residue action is I.
- `decompositionGroupResidueAction_surjective`: the residue action is surjective.
- `decompositionResidueExtension_normal` (instance): λ/κ is normal.
- `decompositionGroupResidueAction_shortExact`: the three exactness statements together.
- The residue action fixes the image of the residue field of Z.

## Proof

A is given the discrete topology. D is closed in the profinite Galois group, hence compact, and its action on A is locally constant, since each element of A generates a finite extension of K. A is then integral over A^D, so the contraction of a maximal ideal is maximal. Surjectivity and normality come from the profinite results `Ideal.Quotient.stabilizerHom_surjective_of_profinite` and `Ideal.Quotient.normal_of_profinite`.

## Watch for

- The target of the sequence is the group of κ-automorphisms of λ. The file proves λ/κ normal but not separable.
- κ is the residue field of the decomposition field. The file does not compare it with the residue field of K.
- Surjectivity and normality need L/K Galois, while the description of the kernel does not.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`: the Lean file is the source byte for byte (SHA-256 `dbcce4afecea7521414160af351b3dc2991ca2e763b81026095d981707621fa3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
