# Independence of the reciprocity isomorphism from the chosen embedding

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L / K`, the library builds the reciprocity isomorphism by realizing `L` inside `SeparableClosure K` through a `K`-embedding `i` and transporting the abstract class-formation reciprocity map. This file proves that the result does not depend on `i`. Two embeddings differ by an automorphism of the separable closure, and the abstract naturality of reciprocity under conjugation supplies the comparison.

## Main definitions and results

- `finiteGaloisEmbeddingConjugator K L i j`: an automorphism `σ` of `SeparableClosure K` with `σ ∘ i = j`, extending the isomorphism `i(L) ≅ j(L)` (`finiteGaloisEmbeddingConjugator_apply`, `finiteGaloisEmbeddingConjugator_comp`, `finiteGaloisFieldRange_conjugator`).
- `finiteGaloisClosedFixingSubgroup_conjugator`: conjugating the fixing subgroup of `i(L)` by `σ⁻¹` gives that of `j(L)`; the inverse reflects the library's right-exponent convention. `finiteGaloisBase_conjugator`: the base subgroup is invariant under every conjugation.
- `finiteGaloisConjugationOfEmbeddings`: the induced isomorphism between the two abstract extension quotients; on a representative `τ` it gives the class of `σ τ σ⁻¹` (`finiteGaloisConjugationOfEmbeddings_mk`).
- `finiteGaloisNormConjugationOfEmbeddings`: the induced map on the abstract finite norm quotients; it fixes the class of every unit of `K` (`finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit`).
- `finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation` (and its additive form) and `finiteNormQuotientEquivEmbeddedNormQuotient_conjugation`: the identifications with `Gal(L / K)^ab` and with the ordinary norm quotient `Kˣ / N(Lˣ)` are compatible with these maps.
- `extensionQuotientCongr`, `finiteNormQuotientCongr`: transport of quotients along equalities of closed subgroups.
- `concreteReciprocityAddEquivOfEmbedding_eq`, `concreteReciprocityEquivOfEmbedding_eq`, `concreteNormResidueSymbolOfEmbedding_eq`: for any embeddings `i`, `j`, the transported reciprocity isomorphism (additive and multiplicative forms) and the norm residue symbol built from `i` and from `j` coincide.

## Proof

The middle square of the comparison is the abstract naturality theorem `DegreeData.normResidueNaturality_conjugation`, combined with a private transport lemma for equal closed subgroups. The two outer squares are the compatibilities listed above. A pointwise diagram chase (`reciprocityTransport_pointwise`, private) concludes.

## Points to watch

- The independence theorems are stated for arbitrary degree data `D`, valuation data `v`, and a hypothesis `hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K)`. The class field axiom is an input here, not proved in this file.
- No local-field hypothesis on `K` appears in this file; `K` is any field and `L / K` any finite Galois extension, both in universe `0`.
- The file installs `intrinsicAbsoluteGaloisT2` as a local instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean`: the Lean file is the source byte for byte (SHA-256 `7ac3f15e714ff3948ca105ad9b58ff81c451fd0f4ece984f023026958cddd12f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
