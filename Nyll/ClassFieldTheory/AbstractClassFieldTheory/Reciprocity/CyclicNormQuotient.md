# Cyclic norm quotients as degree-zero Tate cohomology

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite cyclic extension of abstract fields: `G_L` is normal in `G_K` with finite quotient, and `g` generates that quotient. The file identifies the norm quotient `A_K / N(A_L)`, where `N` is the relative norm from `L` to `K`, with the degree-zero Tate group of `A_L`, viewed as a representation of `G(L/K)`. Under the class field axiom, this gives finiteness of the norm quotient and computes its order.

## Constructions

- `cyclicFixedCycleEquiv`: `A_K` is isomorphic to the kernel of `ρ(g) − 1` on `A_L`.
- `cyclicNormClassHom`: the resulting map from `A_K` to the concrete quotient of this kernel by the image of the norm. Its kernel is exactly `N(A_L)` (`cyclicNormClassHom_ker`), and it is surjective (`cyclicNormClassHom_surjective`). `cyclicFixedCycleEquiv_relativeNorm` matches the relative norm with the first differential of the cyclic complex.
- `cyclicFiniteNormQuotientEquivTateHZero`: the composite isomorphism `FiniteNormQuotient A K L ≃+ tate M 0`, where `M` is `A_L` as a representation of `G(L/K)`. It passes through the concrete quotient (`cyclicFiniteNormQuotientEquivConcrete`, `cyclicConcreteEquivTateHZero`).

## Consequences of the class field axiom

These results assume `hcf : SatisfiesClassFieldAxiom A` and that `K` has finite index in the base field.

- `finiteNormQuotient_finite_of_classFieldAxiom` (also under the name `finiteNormQuotientFiniteOfClassFieldAxiom`): the norm quotient is finite.
- `finiteNormQuotient_card_of_classFieldAxiom`: it has order `[L : K]`.
- `cyclicReciprocity_card_equality`: `G(L/K)`, viewed additively, and the norm quotient have the same order.

`additiveExtensionQuotient_card` gives `|G(L/K)| = [L : K]` without any axiom.

## Watch for

- The class field axiom is a hypothesis, not proved here. Finiteness and the order of `Ĥ⁰` are taken from it.
- The identification uses the chosen generator `g`. The Tate groups are `IntegralGroupCohomology.Universe.tate`, defined in an imported file; the homology of the cyclic norm complex is identified with them by the imported `normHomologyEquivTateZero`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `508c20ed5bcb2861f92c121beb4b985f0190c0dccde2babd58147c84d3865b8a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
