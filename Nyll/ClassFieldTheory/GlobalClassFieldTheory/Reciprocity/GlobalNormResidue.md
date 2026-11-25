# The global norm-residue symbol

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension L/K of number fields, the file constructs the global norm-residue isomorphism from the quotient of C_K by the idele-class norms from L to Gal(L/K), where C_K is the idele class group. It specializes the library's abstract reciprocity for class formations to the idele-class formation over ℚ, with the cyclotomic degree datum and, as valuation data, the cyclotomic valuation, and then defines the norm-residue homomorphism on C_K.

## Main definitions and results

- `globalNormResidueIdeleClassCommGroup` and `globalNormResidueIdeleClassIsMulCommutative`: fix the commutative group structure on C_F used for norm quotients (local instances).
- `numberFieldTowerReciprocityFiniteAbstractField K L`: K realized as a finite abstract field, the subgroup `numberFieldTowerBaseSubgroup K L` of the absolute Galois group of ℚ (taken on `SeparableClosure ℚ`).
- `numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup`: the abelianized abstract extension quotient is Gal(L/K).
- `numberFieldTowerAbstractNormResidueGaloisEquiv`: the abstract norm-residue symbol `rationalCyclotomicDegreeData.normResidueSymbol`, for `rationalIdeleClassRepresentation` with valuation data `rationalCyclotomicIdeleClassValuationData`, followed by that comparison.
- `globalNormResidueEquiv K L`: an additive equivalence `Additive (C_K ⧸ (ideleClassNorm K L).range) ≃+ Additive Gal(L/K)`, the inverse of the comparison `numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient` followed by the abstract symbol. `globalNormResidueEquiv_finiteReciprocityHom` (simp) says it inverts the abstract reciprocity map; `globalReciprocityEquiv` is its inverse.
- `globalNormResidueMonoidHom K L`: the homomorphism C_K → Gal(L/K), the quotient map followed by `globalNormResidueEquiv`.
- `globalNormResidueMonoidHom_eq_one_iff`, `globalNormResidueMonoidHom_ker`: the kernel is the image of the idele-class norm. `globalNormResidueMonoidHom_surjective`. `ideleClassNorm_index_eq_finrank_abelian`: the norm subgroup has index [L : K].
- `globalNormResidueMonoidHom_eq_maximalUnramifiedRestriction`: if the abstract realization of L/K is unramified for `rationalCyclotomicDegreeData` (hypothesis `hUnramified`), the symbol of c is the finite restriction of the maximal-unramified norm-residue symbol of c.

## Proof

All the content is in the abstract theory: the class field axiom for the rational idele-class formation (imported `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`) feeds the abstract norm-residue symbol, which is an isomorphism. Kernel, surjectivity and index then follow formally from the definition as an isomorphism composed with a quotient map.

## Points to watch

- The symbol is defined through class formations, not from local Artin maps; this file does not compare the two.
- The equivalences are stated between `Additive` types, so the groups are written additively.
- "Unramified" in `hUnramified` is the abstract notion relative to the cyclotomic degree datum, not a condition on primes of K.
- The index formula is proved only for abelian L/K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalNormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `e749bcd2d43e4f41dcb5046d0dcb9a03d1957cf07d61c6664eca6bdecbc57e2b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
