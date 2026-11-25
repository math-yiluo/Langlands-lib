# Transfer input for the principal ideal theorem: the Hilbert tower

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTransfer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, H its selected small Hilbert class field, and H' the small Hilbert class field of H, the second stage of the library's selected tower. Extend an idele class of K to H. The file proves that the result lies in the small-Hilbert norm subgroup of H, which an imported result identifies with the norm range from H'. This is the idelic form of the middle vertical arrow in the diagram of the principal ideal theorem. It is obtained by specializing the abstract Witt-transfer capitulation to the rational idele class formation.

## Main definitions and results

- `smallHilbertClassFieldBaseSecondNormRangeContainment K`: the proposition that the range of `ideleClassExtension` from the fixed-field copy `smallHilbertClassFieldBase K` to H lies in `smallHilbertClassFieldNormSubgroup (K := smallHilbertClassField K)`.
- `smallHilbertClassFieldBase_ideleClassExtension_range_le_secondNormRange`: that proposition holds.
- `smallHilbertClassFieldSecondNormRangeContainment K` and `smallHilbertClassField_ideleClassExtension_range_le_secondNormRange`: the same containment for idele classes of K itself, and its proof.

## Proof

1. The tower K ⊆ H ⊆ H' is realized as a finite Galois extension `smallHilbertTowerGaloisRealization` in Gal(ℚ̄/ℚ). An imported result says its maximal abelian subextension is the first stage H.
2. In the rational idele class formation, whose class field axiom is supplied by the imported `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`, the abstract result `intermediateNormQuotientInclusion_commutator_eq_zero` applies. It says the inclusion of norm quotients from K to H is zero.
3. The `RationalFiniteNormTransfer` files turn this zero class into the statement that each extended class lies in the norm range of the fixed fields.
4. An imported equality, `smallHilbertTowerSecondStage_ideleClassNorm_range`, identifies that norm range with the small-Hilbert subgroup of H.
5. The statement for K follows because extension along the copy of K factors through it. A private lemma checks that extension ranges descend along the lower leg of a Galois tower.

## Points to watch

- Both containments are `@[irreducible]` definitions of propositions. To use them, unfold the definition.
- The statement concerns idele classes and the small-Hilbert norm subgroup of H. Translating it into the capitulation of ideal classes of K in H is not done in this file.
- The tower is the library's selected construction inside the separable closure of ℚ. Most of the file is private plumbing between the abstract fixed fields and the concrete number fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/PrincipalIdealTransfer.lean`: the Lean file is the source byte for byte (SHA-256 `56dd2dd56de4b3d294b8a1e3fa556ddb1f511db2de0906787bb42ed253704bca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
