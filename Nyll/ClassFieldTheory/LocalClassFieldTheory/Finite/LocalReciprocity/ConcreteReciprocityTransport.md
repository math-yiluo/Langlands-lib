# Transport of abstract reciprocity to a finite Galois extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file performs the final comparison step of the local reciprocity law in the library. Given the data of the abstract class formation for a field `K` (the absolute Galois group of `K`, acting on the units of `SeparableClosure K`), it transports the abstract reciprocity isomorphism through a realization of a finite Galois extension `L / K` inside `SeparableClosure K`, and obtains `Gal(L / K)^ab ≃ Kˣ / N(Lˣ)`, with `N` the norm from `L` to `K`, and the norm residue symbol.

## Main definitions and results

- `finiteGaloisAbstractExtensionOfEmbedding K L i`: the abstract finite Galois subextension determined by a `K`-embedding `i : L → SeparableClosure K`, namely the closed fixing subgroup of `i(L)`. `finiteGaloisAbstractExtension K L` uses the chosen embedding `AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L`.
- `concreteReciprocityAddEquivOfEmbedding`: the composite of `Gal(L / K)^ab ≃` the abelianized abstract extension quotient, the abstract reciprocity isomorphism `DegreeData.abstractReciprocityEquiv`, and the comparison `finiteNormQuotientEquivEmbeddedNormQuotient` with the ordinary norm quotient `NormQuotient K L`. `concreteReciprocityEquivOfEmbedding` is its multiplicative form.
- `concreteNormResidueSymbolOfEmbedding`: the map `Kˣ → Gal(L / K)^ab`, the quotient map `normClass K L` followed by the inverse of reciprocity.
- `concreteReciprocityAddEquiv`, `concreteReciprocityEquiv`, `concreteNormResidueSymbol`: the same three objects for the chosen embedding.
- `concreteNormResidueSymbol_surjective` and `concreteNormResidueSymbol_ker`: the norm residue symbol is surjective, and its kernel is exactly the norm subgroup `localNormSubgroup K L`.

## Points to watch

- Apart from `finiteGaloisAbstractExtensionOfEmbedding` and `finiteGaloisAbstractExtension`, every definition and both theorems take degree data `D`, valuation data `v` and `hcf : SatisfiesClassFieldAxiom` for the units of `SeparableClosure K`. The docstrings describe these as the structures constructed earlier in the proof, but here they are parameters: the class field axiom is a hypothesis of this file, not proved in it.
- No local-field hypothesis on `K` appears in this file, and the universes of `K` and `L` are arbitrary.
- The definitions without `OfEmbedding` depend a priori on the chosen embedding; this file does not compare different embeddings.
- The coefficient module is `(SeparableClosure K)ˣ`; the header stresses that this matters for imperfect fields of positive characteristic.
- A local instance makes the absolute Galois group Hausdorff (`krullTopology_t2`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean`: the Lean file is the source byte for byte (SHA-256 `5ac3badccc0374b990533f38b546a4bd40da12b8b595a67c694c8e576e7f5ce4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
