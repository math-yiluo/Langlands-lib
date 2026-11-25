# The idele-class formation over ℚ satisfies the class-field axiom

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves one theorem: the absolute idele-class representation over ℚ, `rationalIdeleClassRepresentation`, satisfies the abstract class-field axiom `SatisfiesClassFieldAxiom` of the library's theory of class formations. Concretely, for every finite layer K and every normal finite layer L ⊆ K whose quotient `K/L` is cyclic with a chosen generator, the fixed representation `M` of `K/L` has finite Tate cohomology in degrees 0 and −1, with `#H⁰` equal to the abstract degree `[K : L]` and `#H⁻¹ = 1`.

## Main result

- `Reciprocity.rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`.

## Proof

The fixed fields `F ⊆ E` of K and L inside `SeparableClosure ℚ` are number fields with E/F Galois, and the abstract quotient is identified with `Gal(E/F)`. Through `rationalAbstractExtensionIdeleClassEquiv`, `M` is isomorphic to the restriction of the relative idele class group `RelativeIdeleGroup.ClassGroup F E`. Tate cohomology in degrees 0 and −1 is then compared through the finite-cyclic descriptions (norm and difference maps), and the imported cyclic computation `ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic` gives the orders `[E : F]` and 1. The data are packaged with `ClassFieldAxiomCohomologyData.ofOriginal`.

## Points to watch

- The base field is ℚ only; the layers are the library's abstract open subgroups, related to number fields through fixed fields in the separable closure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassFormation.lean`: the Lean file is the source byte for byte (SHA-256 `714bb4d9835210bf4e8df2cdefcbc4ae99209f7c19b66c98d8adbac6845c45c4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
