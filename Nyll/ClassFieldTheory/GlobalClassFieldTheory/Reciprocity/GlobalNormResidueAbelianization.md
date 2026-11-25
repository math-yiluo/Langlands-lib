# Global reciprocity for finite Galois extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an arbitrary finite Galois extension L/K of number fields, the file constructs the global norm-residue isomorphism from the quotient of C_K by the idele-class norms from L to Gal(L/K)^ab, with target the abelianization of the Galois group, and shows that for abelian extensions it reduces to the norm-residue isomorphism onto Gal(L/K).

## Main definitions and results

- `numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization`: the abelianized abstract extension quotient of the realization of L/K is Gal(L/K)^ab; its simp lemma sends the class of an abstract automorphism to the class of the corresponding automorphism of L.
- `numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv`: the abstract norm-residue symbol of the rational idele-class formation (`rationalCyclotomicDegreeData.normResidueSymbol`) followed by that comparison.
- `globalNormResidueAbelianizationEquiv K L`: an additive equivalence `Additive (C_K ⧸ (ideleClassNorm K L).range) ≃+ Additive (Abelianization Gal(L/K))`. `globalNormResidueAbelianizationEquiv_finiteReciprocityHom` (simp) says that on the abstract reciprocity class of an abstract automorphism it gives the class of the corresponding automorphism in Gal(L/K)^ab; `globalReciprocityAbelianizationEquiv` is its inverse.
- `globalNormResidueAbelianizationMonoidHom K L`: the homomorphism C_K → Gal(L/K)^ab (quotient map followed by the equivalence). It is surjective, and its kernel is the image of `ideleClassNorm K L` (`globalNormResidueAbelianizationMonoidHom_ker`, `_eq_one_iff`).
- `ideleClassNorm_index_eq_galoisAbelianization_card`: the image of `ideleClassNorm K L` has index |Gal(L/K)^ab|.
- `globalNormResidueAbelianizationIdeleMonoidHom`: the pullback of the class map to the idele group I_K. It is trivial on principal ideles, surjective, and its kernel is the preimage of the norm subgroup.
- Abelian specialization: for F ⊆ E finite abelian, composing with the inverse of `Abelianization.equivOfComm` turns `globalNormResidueAbelianizationEquiv`, `globalNormResidueAbelianizationMonoidHom` and the idele-level map into `globalNormResidueEquiv`, `globalNormResidueMonoidHom` and its pullback, and precomposing `globalReciprocityAbelianizationEquiv` with `Abelianization.equivOfComm` itself gives `globalReciprocityEquiv` (theorems with suffix `_abelianSpecialization`).

## Proof

The construction is the same three-step composite as in the abelian case: the comparison `numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient` between the abstract finite norm quotient and C_K / N C_L, the abstract norm-residue symbol, and the Galois comparison. The abelian specialization is checked on the image of the abstract finite reciprocity map, which is surjective (`abstractReciprocity_finiteReciprocityHom_surjective`), where both sides are given by the simp lemmas above.

## Points to watch

- The content comes from the abstract class formation theory and the imported class field axiom `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`; no local Artin maps appear.
- For non-abelian L/K the index is |Gal(L/K)^ab|, not [L : K].
- Triviality of the idele-level map on principal ideles holds by construction, since that map is defined through C_K; it is not a product formula for local symbols.
- The equivalences are stated between `Additive` types.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalNormResidueAbelianization.lean`: the Lean file is the source byte for byte (SHA-256 `dbd9c02b118fbb7b65cf4ac7e38a4d69ffe8965a31de7e6aabdec15437f96ac8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
