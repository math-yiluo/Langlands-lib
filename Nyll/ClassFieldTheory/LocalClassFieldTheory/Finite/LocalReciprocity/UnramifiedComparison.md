# Abstract and concrete unramified Frobenius

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library builds local reciprocity from an abstract class-formation framework on the absolute Galois group of K, with a residue datum `localResidueDatum K` and a fixed valuation subring `localSeparableValuationSubring K` of `SeparableClosure K`. A finite Galois extension L/K enters through a K-embedding i : L → K^sep, which gives an abstract extension `finiteGaloisAbstractExtensionOfEmbedding K L i` and a quotient equivalence `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i` onto Gal(L/K). The file shows that, for an unramified L/K, the abstract notions of unramifiedness and of Frobenius match the concrete ones defined through valuations.

## Main definitions and results

Unless said otherwise, K and L are nonarchimedean local fields in `Type`, L/K finite Galois, the valuation of L extending that of K.

- `intrinsicFiniteAbstractBase_residueDegree_eq_one`: the abstract base field has residue degree one (K in any universe).
- Instances `finiteGaloisLocalField_integerRing_isIntegralClosure` and `finiteGaloisLocalField_integerRing_moduleFinite`: 𝒪_L is the integral closure of 𝒪_K in L and is finite over 𝒪_K (K, L in any universes).
- `localSeparableValuationSubring_comap_embedding`: for L/K finite separable with a valuation on L extending that of K (L need be neither Galois nor a local field), the pullback along i of the fixed valuation subring of K^sep is the valuation subring of L.
- `finiteGaloisResidueEmbeddingOfEmbedding`: the residue field of L (here too L needs no local-field structure) embedded, by reduction of i, into the residue field of K^sep chosen by the framework; `finiteGaloisResidueEmbeddingOfEmbedding_residue` computes it on residues, and `finiteGaloisResidueEmbeddingOfEmbedding_equivariant` shows it intertwines the residue action of Gal(L/K) with that of the absolute Galois group.
- `finiteGaloisAbstractExtensionOfEmbedding_isUnramified`: if L/K is unramified (`IsUnramifiedValuedExtension K L`), the abstract extension is unramified for `localResidueDatum K`.
- `finiteGaloisAbstractUnramifiedFrobenius_eq_arithmeticFrobenius`: for L/K unramified, the abstract unramified Frobenius of the residue datum corresponds to `arithmeticFrobeniusOfUnramifiedValuation K L`.

## Proofs

The pullback statement rests on uniqueness of the extension of the valuation of a complete discretely valued field to a finite separable extension. For the Frobenius, a degree-one element of the absolute Galois group is chosen (`Classical.choose`, from surjectivity of the normalized degree); such an element acts on the residue closure by x ↦ x^q, q the cardinality of the residue field of K. The equivariant residue embedding moves this to the residue field of L, and an element of Gal(L/K) of an unramified extension is determined by its residue action.

## Caveats

- The two instances on 𝒪_L are global; the docstring stresses that they are derived from the valuation extension, not assumed.
- The abstract objects (residue datum, abstract base and extensions) are the library's own class-formation framework, not Mathlib notions.
- The embedding i is a parameter of every statement after the instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean`: the Lean file is the source byte for byte (SHA-256 `d761e16794639ee3ec1acdb74a3d5d06cd44f29e85f63ec838f9d36e7df11064`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
