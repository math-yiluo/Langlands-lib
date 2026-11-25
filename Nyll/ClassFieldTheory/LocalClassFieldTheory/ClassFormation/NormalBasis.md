# Graded pieces of the normal-basis lattice are regular modules

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension, `K` a nonarchimedean local field with uniformizer `π` (the chosen `chosenIntegerRingUniformizer`) and residue field `𝓀_K`. Let `M = chosenNormalBasisIntegerLattice K L` be the `𝒪_K`-lattice spanned by the Galois orbit of the normal basis `IsGalois.normalBasis K L`. The file shows that each graded piece `πⁿM / πⁿ⁺¹M` (`chosenNormalBasisLatticeSuccQuot K L n`), with its Galois action, is the right-regular module of functions `Gal(L/K) → 𝓀_K`, so that its Herbrand groups vanish.

## Main definitions

- `chosenNormalBasisIntegerLatticeBasis`: the normal-basis orbit as an `𝒪_K`-basis of `M` indexed by `Gal(L/K)` (via `span_normalBasis_eq_chosenNormalBasisIntegerLattice`).
- `chosenNormalBasisIntegerLatticeMulPowLinearEquiv n`: multiplication by `πⁿ`, an `𝒪_K`-isomorphism `M ≅ πⁿM`.
- `chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv n`: `πⁿM / πⁿ⁺¹M ≅ M / πM`, by removing the factor `πⁿ`.
- `chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv n`: an additive isomorphism `πⁿM / πⁿ⁺¹M ≅ (Gal(L/K) → 𝓀_K)`, sending a class to its basis coordinates reduced modulo `𝓂_K`, with the index replaced by its inverse.
- `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`, `galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction n`: the Galois action on `M` and the induced action on each graded piece.

## Main results

- `chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup`: the coordinate of `τ x` at `σ` is the coordinate of `x` at `τ⁻¹σ`.
- `chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes`: in the inverted coordinates, the coordinate of `τ • q` at `σ` is that of `q` at `στ`.
- `chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton`: the degree-zero Herbrand group of each graded piece, viewed multiplicatively, is trivial.
- `chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton`: for a generator `τ` of `Gal(L/K)`, the degree −1 Herbrand group with respect to `τ` is trivial.

## Proofs

A Galois element permutes the basis by left translation, which gives the coordinate rule; inverting the index turns it into the right-regular rule. The vanishing then comes from the general results `herbrandH0_subsingleton_of_addEquiv_rightRegularFunction` and `herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunction`.

## Points to note

- `M` depends on the normal basis chosen by Mathlib; it is not canonical. The scaling maps `M ≅ πⁿM` use the chosen uniformizer.
- The action on a graded piece is defined by transport through `M / πM`; on representatives it agrees with the field automorphism (`chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe`).
- The identification with functions is additive only, and the Herbrand groups are those of the multiplicative copy `Multiplicative (πⁿM / πⁿ⁺¹M)`.
- The degree-zero vanishing needs no cyclicity; the degree −1 statement assumes a generator.
- `K` and `L` are taken in the same universe (`K L : Type u`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`: the Lean file is the source byte for byte (SHA-256 `ee9348c6f933e5cf243ec7dd68b035d91709ca63278194a89721b9778f9a9914`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
