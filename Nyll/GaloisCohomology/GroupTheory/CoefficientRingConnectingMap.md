# Connecting maps under a change of coefficient ring

Module `Nyll.GaloisCohomology.GroupTheory.CoefficientRingConnectingMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

When a representation is transported along a ring isomorphism `e : R ≃+* S` (scalars restricted along e, same carrier and action), the comparison isomorphisms of group cohomology and of Tate cohomology are compatible with the connecting maps of short exact sequences. The file proves this in every degree.

## Main results

R and S are commutative rings; R, S, G and the carriers of the representations lie in one universe u, and X is a short exact sequence of S-linear representations of G.

- `groupCohomology.coefficientRingComplexNatIso`: the identity of cochains is a natural isomorphism between the cochain complex functor followed by restriction of scalars and transport followed by the cochain complex functor.
- `groupCohomology.coefficientRingIso_δ`: the connecting map `Hⁱ(X₃) → Hʲ(X₁)` (with `i + 1 = j`), after restricting scalars, followed by the comparison isomorphism `coefficientRingIso`, equals the comparison followed by the connecting map of the transported sequence. `groupCohomology.δ_coefficientRingIso_inv` is the same with the inverse isomorphisms.
- For G finite: `TateCohomology.coefficientRingComplexNatIso`, `TateCohomology.coefficientRingIso_δ` and `TateCohomology.δ_coefficientRingIso_inv`, the same statements for Tate cohomology and its connecting maps `Ĥⁱ → Ĥⁱ⁺¹`, for every i ∈ ℤ, including the step through the norm map from degree −1 to degree 0.

## Proof

The natural isomorphism identifies the two short exact sequences of complexes. The connecting maps then agree by Mathlib's naturality of the homology sequence connecting map (`HomologicalComplex.HomologySequence.δ_naturality`) and by the fact that the exact functor of restricting scalars commutes with connecting maps (`map_δ_eq`, from the library's homological algebra files).

## Watch for

The comparison isomorphisms themselves are defined in the coefficient-ring equivalence files for cohomology, homology and Tate cohomology; this file adds their naturality on complexes and their compatibility with connecting maps.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/CoefficientRingConnectingMap.lean`: the Lean file is the source byte for byte (SHA-256 `b63496e16aad2716549965f51314bfdf9d1951a43d824ac4d761d5d511fba4e2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
