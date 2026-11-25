# The changed-uniformizer level as a Frobenius fixed field

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let E be the completed p-adic Lubin–Tate level at level n, a finite extension of the completed maximal unramified extension A of ℚ_p, and u a unit of ℤ_p. The completed Frobenius lift indexed by u⁻¹ (Frobenius on A, a prescribed action on the standard primitive point) is a ℚ_p-automorphism δ of E. The file shows that the fixed field of δ is ℚ_p(θ), θ the changed theta value, and that it is isomorphic to the n-th standard Lubin–Tate level for the uniformizer u·p; it transports the norm formula N(−θ) = u·p.

## Main definitions and results

- `padicCompletedChangedUniformizerFrobeniusAlgEquiv`: δ as a ℚ_p-automorphism of E; `padicCompletedChangedUniformizerFrobeniusSubgroup` its cyclic group; `padicCompletedChangedUniformizerFixedField` the fixed field D.
- `padicChangedUniformizerThetaValue_mem_completedFixedField`, `padicChangedUniformizerLevelEmbedding_mem_completedFixedField`: θ, and the image of the changed level under its embedding into E, lie in D. `padicChangedUniformizerLevelToCompletedFixedField` is the embedding into D, sending the generator to θ.
- `padicCompletedChangedUniformizerFrobenius_fixed_mem_adjoin_theta` and `padicCompletedChangedUniformizerFixedField_eq_adjoin_theta`: D = ℚ_p(θ).
- `padicChangedUniformizerThetaValue_isIntegral_padicBase`, `padicChangedUniformizerThetaValue_minpoly_padicBase`: θ is integral over ℚ_p with minimal polynomial the changed primitive Lubin–Tate polynomial.
- `padicCompletedChangedUniformizerFixedField_finrank`: [D : ℚ_p] = (p − 1)·p^n.
- `padicChangedUniformizerLevelEquivCompletedFixedField`: a ℚ_p-isomorphism from the changed level onto D, sending the generator to θ.
- `padicCompletedChangedUniformizerPrimeElement`: θ as an element of D.
- `padicCompletedChangedUniformizer_norm_neg_primeElement`: the norm from D to ℚ_p of −θ is the changed uniformizer u·p.

## Proofs

For D ⊆ ℚ_p(θ): write a fixed x in the power basis of θ over A. Since δ fixes θ and acts on A by Frobenius, fixedness forces every coefficient to be Frobenius-fixed, hence in ℚ_p by the fixed-field theorem for the completed unramified Frobenius. The degree comes from the minimal polynomial; the embedding is then an isomorphism by comparing dimensions, and the norm formula is transported from the finite changed level.

## Watch for

- Per the module comment, the norm formula is obtained by transport from the finite changed level, with no comparison hypothesis.
- The ℚ_p-algebra structure on D used for the degree is installed by local instances in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedUniformizerFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `958101af3e5b820c6cd6dc20d17a2e54747c76d59747f897c5620c86afb05650`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
