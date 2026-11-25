# Naturality of the global norm-residue map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file compares global norm-residue maps built in the rational absolute class formation, where `Gal(ℚˢᵉᵖ/ℚ)` acts on `rationalIdeleClassRepresentation` with the degree data `rationalCyclotomicDegreeData`. It shows that two constructions of the map agree, proves the compatibility of the map with idele-class norm and restriction of automorphisms, and records a same-base naturality statement for an arbitrary class formation.

## Main results

- `globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion`: for a finite abstract field `H` of `Gal(ℚˢᵉᵖ/ℚ)` and a finite abelian subextension `P`, take the fixed fields `F ⊆ E` and the inclusion `j : E → ℚˢᵉᵖ`. Then the norm-residue map built from the embedding `j` equals the intrinsic fixed-field map `abstractFixedFieldGlobalNormResidueMonoidHom H P`.
- `numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction`: take number fields with towers `K ⊆ K' ⊆ L'` and `K ⊆ L ⊆ L'`, `L/K` and `L'/K'` finite abelian Galois, and an embedding `j : L' → ℚˢᵉᵖ`. The identifications of the abelianized abstract quotients with `Gal(L'/K')` and `Gal(L/K)` turn the abstract restriction `normResidueNaturalityAbelianizedRestriction` into ordinary restriction of automorphisms.
- `numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm`: if `K'/K` is finite Galois, the class-formation `relativeNorm` of the image of `c : IdeleClassGroup K'` is the image of the idele-class norm `ideleClassNorm K K' c`.
- `globalNormResidueMonoidHomOfEmbedding_norm_restriction`: under all the hypotheses above, restriction `Gal(L'/K') → Gal(L/K)` composed with `globalNormResidueMonoidHomOfEmbedding K' L' j` equals `globalNormResidueMonoidHomOfEmbedding K L jLower` composed with `ideleClassNorm K K'`, as monoid homomorphisms `IdeleClassGroup K' → Gal(L/K)`, where `jLower` is `j` composed with `L → L'`.
- `normResidueSymbol_restriction_sameBase`: for any compact, Hausdorff, totally disconnected group `G`, degree data, module, valuation data and class field axiom, and closed subgroups `L ≤ M` inside a finite abstract field `K`, both normal in `K` and `L` of finite index: the norm-residue symbol for `L`, followed by abstract restriction to `M`, equals the norm projection from the `L`-norm quotient to the `M`-norm quotient followed by the norm-residue symbol for `M`.

Most of the file consists of private lemmas transporting dependent data along equalities of closed subgroups.

## Proofs

The first theorem compares the two quotient-to-Galois maps on coset representatives. The norm-restriction theorem specializes the imported `DegreeData.normResidueNaturality_norm_restriction`, using the two comparisons above. The same-base theorem is that naturality with the base unchanged.

## Points to watch

- The norm comparison and the norm-restriction compatibility assume `K'/K` Galois (`IsGalois K K'`), more than the classical statement, which holds for any finite `K'/K`.
- The maps are built from the chosen common embedding `j` of `L'`; the lower field is embedded through `j`.
- The rational results use the class field axiom term `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom` from elsewhere in the library.
- `normResidueSymbol_restriction_sameBase` covers only restriction over the same base field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalNormResidueNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `422a68dfee1117b8cad0927b3130beff1d3af957097d7c738407915c175096a0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
