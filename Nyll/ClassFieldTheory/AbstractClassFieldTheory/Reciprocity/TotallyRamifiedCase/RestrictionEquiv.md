# The lower Galois group of the auxiliary totally ramified tower

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois totally ramified extension of abstract fields, with `K : FiniteResidueAbstractField D` (over a compact Hausdorff group `G` with degree map `D`), q ∈ G(L/K), M the auxiliary finite Galois extension built from q, and M₀ the maximal unramified subextension of M/K. This file identifies G(M/M₀) with G(L/K).

- `abstractReciprocityTotallyRamifiedRestrictionEquiv`: restriction gives a group isomorphism G(M/M₀) ≃ G(L/K). It is the restriction isomorphism for totally ramified extensions, applied with the inertia condition that holds because M lies in the maximal unramified extension of L.
- `abstractReciprocityTotallyRamifiedLowerDegree_eq`: hence [M : M₀] = [L : K].
- `abstractReciprocityTotallyRamifiedLowerGenerator`: the element of G(M/M₀) corresponding to q; it maps to q (`…RestrictionEquiv_lowerGenerator`), and generates G(M/M₀) whenever q generates G(L/K) (`…LowerGenerator_generates`).

The generator statement takes the generation of G(L/K) by q as the hypothesis `hq`; the constructions themselves only need q ∈ G(L/K).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `ce15656c4dd63072339998e16094d7982f4189ee0a48452acea7252b5ce15af8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
