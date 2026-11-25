# Normalized degree and the Frobenius of an abstract field

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an abstract field `K` (a closed subgroup `G_K` of `G`, with degree datum `d : G → ℤ̂`) of finite residue degree `f_K`, the file builds the normalized degree `d_K = (1/f_K) d` on `G_K` and defines the Frobenius of `K` as the class in `G_K / I_K` sent to `1` by `d_K`. Division by `f_K` is done only after proving `d(G_K) = f_K ℤ̂`.

## Main definitions and results

- `fieldImageAdd_eq_mulNat_range`: for `K` with finite residue quotient, `d(G_K) = f_K ℤ̂`; `fieldImageAdd_index` gives index `f_K`.
- `normalizedDegree`: the continuous homomorphism `d_K : G_K → ℤ̂`, with `residueDegree_nsmul_normalizedDegree` (`f_K · d_K = d`), `normalizedDegree_surjective` and `normalizedDegree_ker` (the kernel is the inertia `I_K`).
- `maximalUnramifiedDegreeEquiv`: the isomorphism `G_K / I_K ≃ ℤ̂` induced by `d_K`.
- `frobenius`: the preimage of `1`; `eq_frobenius_iff` is its uniqueness.
- `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`: `f(L/K) · f_K = f_L`, and `frobeniusRestrictionNaturality_residueDegree`: `f(L/K) = f_L / f_K` (natural-number division, exact here).
- `maximalUnramifiedRestriction`: the map `G_L / I_L → G_K / I_K` induced by inclusion when `G_L ≤ G_K`.
- `frobeniusRestrictionNaturality_normalizedDegree`: on `G_L`, `d_K = f(L/K) · d_L`; `frobeniusRestrictionNaturality_quotient_square` is its quotient form.
- `frobenius_restriction_eq_power`: the restriction of `φ_L` is `φ_K ^ f(L/K)`.

The residue-degree identity comes from the cardinal identity of the fields file; the rest follows by cancelling the injective multiplication by `f_K` on `ℤ̂`.

## Points to watch

- `G_K / I_K` here is the quotient of the subgroup `G_K` by `ker d ∩ G_K`; it stands for the Galois group of the maximal unramified extension, but no field is constructed.
- The normalized degree and the Frobenius require `K` bundled with finite residue quotient (`FiniteResidueAbstractField`). The statements comparing `L` and `K` take a `FiniteResidueAbstractExtension`: both fields with finite residue quotient and `L` finite over `K`. `maximalUnramifiedRestriction` needs only the inclusion `G_L ≤ G_K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`: the Lean file is the source byte for byte (SHA-256 `3979410a336cb21407a9fca09f8d6bdf4c04c1e702586f269418ce94929344d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
