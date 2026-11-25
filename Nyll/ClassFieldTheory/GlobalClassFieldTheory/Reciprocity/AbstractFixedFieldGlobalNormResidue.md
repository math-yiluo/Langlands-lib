# Global norm residue maps for embedded fields and fixed fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file transports the abstract norm-residue symbol of the rational absolute idele-class formation (`rationalIdeleClassRepresentation`, with its class field axiom `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`) to genuine isomorphisms onto `Gal(L/K)` from the idele class group `C_K` of a number field modulo the norms from `L`. It does so in two settings: a finite abelian extension `L/K` with an explicitly given embedding `j : L → SeparableClosure ℚ`, and a pair of fixed fields `F ⊆ E` of closed subgroups of `Aut(SeparableClosure ℚ / ℚ)`. Everything stays in one separable closure, so no second embedding is chosen.

## Embeddings

- `numberFieldEmbeddingComparisonAutomorphism i j`: an automorphism of `SeparableClosure ℚ` carrying the embedding `i` of a number field to `j` (existence: `exists_numberFieldEmbeddingComparisonAutomorphism`); conjugation by `numberFieldEmbeddingComparisonAutomorphism j i` carries the fixing subgroup of the image of `i` to that of `j` (`conjugateClosedFixingSubgroup_embeddingRange`).
- For `L/K` finite Galois and `j`: the fixing subgroups `numberFieldEmbeddedBaseSubgroup` and `numberFieldEmbeddedTopSubgroup`, the subextension `numberFieldEmbeddedFiniteGaloisSubextension`, the identification of its quotient with `Gal(L/K)`, and `numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient`, the abstract finite norm quotient as `C_K` modulo the range of `ideleClassNorm K L`, with evaluation lemmas on idele classes.
- `numberFieldEmbeddedBaseSubgroup_le_of_tower`, `numberFieldEmbeddedTopSubgroup_le_of_tower`: in compatible towers `K ⊆ K'`, `L ⊆ L'`, the fixing subgroups reverse the inclusions.

## Norm residue maps

- `globalNormResidueEquivOfEmbedding K L j` and `globalNormResidueMonoidHomOfEmbedding K L j : C_K →* Gal(L/K)`, for `L/K` finite abelian, with evaluation formula `globalNormResidueMonoidHomOfEmbedding_apply`.
- `globalNormResidueEquiv_eq_ofEmbedding_standard`, `globalNormResidueMonoidHom_eq_ofEmbedding_standard`: at the standard embedding `numberFieldSeparableClosureEmbedding L`, these coincide with the library's `globalNormResidueEquiv` and `globalNormResidueMonoidHom`.
- For a finite abstract field `K` and a finite abelian subextension `L` with fixed fields `F ⊆ E`: `abstractFixedFieldGlobalNormResidueEquiv K L`, from `C_F` modulo the range of `ideleClassNorm F E` onto `Gal(E/F)`, its version `ambientFixedGlobalNormResidueAddMonoidHom` on the fixed part of the class formation, and `abstractFixedFieldGlobalNormResidueMonoidHom K L : C_F →* Gal(E/F)`.
- `abstractFixedFieldGlobalNormResidueMonoidHom_eq_one_iff`, `_ker`, `_surjective`: this map is surjective, and its kernel is exactly the range of `ideleClassNorm F E`.

## Proofs

Each equivalence is the composite of the comparison of finite norm quotients with idele-class norm quotients, the abstract symbol `rationalCyclotomicDegreeData.normResidueSymbol`, and the identification of the abelianized abstract quotient with the Galois group. `abstractFixedFieldGlobalNormResidueMonoidHom` instead transports an idele class to the fixed part and applies `ambientFixedGlobalNormResidueAddMonoidHom`, built on `finiteNormClassHom`. The comparison with the existing map is checked on idele classes, using surjectivity of the quotient map, not as an equality of constructions.

## Caveats

- The reciprocity maps come from the abstract class formation; the file does not relate them to Frobenius elements or local symbols.
- The agreement with `globalNormResidueEquiv` is proved only for the standard embedding.
- `numberFieldEmbeddingComparisonAutomorphism` is defined by choice; `rationalEmbeddingSeparableClosureAlgebra`, the algebra induced by an embedding, is deliberately not an instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/AbstractFixedFieldGlobalNormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `c7d68555983a8f0b425ea6ef9c9f44a39eafb07961ab80b2c7d87f16419bb456`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
