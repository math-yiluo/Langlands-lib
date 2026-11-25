# Local compactness of the idele group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file proves that the idele group, with its restricted-product topology, is locally compact. The proof shows that every completion K_v at a finite place is a proper space and that the units of its ring of integers form a compact set, and then applies the theorem that a restricted product of locally compact groups with respect to open subgroups is locally compact when the subgroups are compact at almost all places.

## Main results

- `exists_ringOfIntegers_approximation`: for a finite place v of K (a height-one prime of 𝓞 K) and y ∈ K with v(y) ≤ 1, there is r ∈ 𝓞 K with v(y − r) < 1.
- `GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField`: a ring isomorphism between 𝓞 K ⧸ v and the residue field of K_v. It is induced by the map 𝓞 K → integers of K_v followed by reduction to the residue field. The kernel of this composite is v, and its surjectivity comes from density of K in K_v together with the approximation lemma above.
- `finite_adicCompletion_residueField`: the residue field of K_v is finite, since 𝓞 K ⧸ v is.
- `adicCompletionProperSpace` (instance): K_v is a proper metric space, by Mathlib's criterion (complete, ring of integers a discrete valuation ring, finite residue field).
- `isCompact_finiteLocalUnits`: the units of the ring of integers of K_v form a compact subset of K_vˣ.
- `finiteIdeleGroupLocallyCompactSpace`: `FiniteIdeleGroup K` is locally compact, by Mathlib's `RestrictedProduct.locallyCompactSpace_of_group`.
- `infiniteIdeleGroupLocallyCompactSpace` and `ideleGroupLocallyCompactSpace`: the archimedean factor `InfiniteIdeleGroup K` and the full `IdeleGroup K` are locally compact. Both are found by instance search.

## Points to watch

- `FiniteIdeleGroup K`, `InfiniteIdeleGroup K` and `IdeleGroup K` are the library's own types, defined in `AlgebraicNumberTheory.Idele.Basic` and imported here through `AlgebraicNumberTheory.Idele.Topology`. The finite part has the restricted-product topology with respect to the local unit groups, not the subspace topology from the finite adeles.
- The residue-field isomorphism lives in the namespace `GlobalClassFieldTheory.ClassFieldAxiom`, but it is a complete construction and not an assumed axiom.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/LocallyCompact.lean`: the Lean file is the source byte for byte (SHA-256 `354867424dfa07cf66a78573dc2109251cbda3576047fcf37e2e385ad007ab14`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
