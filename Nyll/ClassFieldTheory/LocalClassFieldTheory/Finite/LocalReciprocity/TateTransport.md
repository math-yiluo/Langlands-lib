# Transport of cyclic Tate complexes

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite cyclic group with generator `g` and a representation `A`, Tate cohomology in degrees 0 and −1 is computed by two short complexes built from the norm map and `g − 1` (Mathlib's `Rep.FiniteCyclicGroup.normHomCompSub` and `subCompNormHom`). This file shows that these complexes, and their homology, are unchanged under the two moves needed to transfer the class field axiom from fixed fields to the abstract class formation.

- `map_cyclicGenerator`: a group isomorphism sends a generator to a generator.
- Reindexing along an isomorphism `e : Q ≃* P` of finite commutative groups: `res_norm_eq` (restriction along `e` has the same norm map), `normHomCompSubResEquivIso` and `subCompNormHomResEquivIso` (the complexes of `Rep.res e A` at `g` and of `A` at `e g` are isomorphic), and their homology versions `normHomCompSubHomologyResEquivIso`, `subCompNormHomHomologyResEquivIso`.
- Isomorphic representations `M ≅ N` of the same group: `normHomCompSubIsoOfRepIso`, `subCompNormHomIsoOfRepIso`, and the homology versions `normHomCompSubHomologyIsoOfRepIso`, `subCompNormHomHomologyIsoOfRepIso`.

For the complex and homology comparisons the groups are commutative and finite and, like the coefficient ring, in `Type`, and `g` is any element; `map_cyclicGenerator` holds for arbitrary groups in any universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean`: the Lean file is the source byte for byte (SHA-256 `332a37d530978128f800c9c87e3189f68213b2eacd82a3f17605e8ce1ecb4811`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
