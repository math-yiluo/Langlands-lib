# Coefficient ring isomorphisms for group homology and Tate cohomology

Module `Nyll.GaloisCohomology.GroupTheory.CoefficientRingHomologyEquivalence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Continuing the comparison for group cohomology, the file shows that transporting a representation along a ring isomorphism `e : R ≃+* S` (scalars restricted along e, same carrier and action) does not change Mathlib's group homology or Tate cohomology. In both cases the comparison is the identity on chains and cochains.

## Main definitions and results

R and S are commutative rings, R, S and G lie in one universe u, and A is an S-linear representation of G.

- `Rep.tateNorm_single_apply`: for G finite, the norm map of the Tate complex sends a single degree 0 chain `single g a` to the function with constant value `N(a)`, the representation norm.
- `groupHomology.coefficientRingChainsIso` and `coefficientRingComplexIso`: the inhomogeneous chain complex of A with scalars restricted along e is isomorphic to that of the transported representation, by the identity on finitely supported chains.
- `groupHomology.coefficientRingIso n`: `Hₙ(G, A)` with scalars restricted is isomorphic to `Hₙ` of the transported representation.
- For G finite: `TateCohomology.coefficientRing_tateNorm` (the norm map in the middle of the Tate complex is compatible), `TateCohomology.coefficientRingComplexIso` (the Tate complexes are isomorphic, cochains in degrees ≥ 0 and chains in negative degrees), and `TateCohomology.coefficientRingIso n` for every n ∈ ℤ.
- `ShortComplex.restrictScalars_homologyClass`: for commutative rings in `Type`, a ring map r, a short complex C over S and a morphism f from C with scalars restricted along r to a short complex D over R, if f sends a cycle z to a cycle w, it sends the homology class of z to that of w.

## Proof

The chain groups are the same finitely supported functions; the differentials agree on single chains, since e preserves the signs. The Tate complex is assembled degree by degree from the cochain and chain comparisons, together with the norm compatibility in the middle.

## Watch for

- The comparisons require the coefficient rings, the group and the carrier in a single universe; `restrictScalars_homologyClass` is stated only for rings in universe 0.
- The isomorphisms are with Mathlib's `groupHomology` and `tateCohomology` of the transported representation, viewed over R; no new homology object is introduced here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/CoefficientRingHomologyEquivalence.lean`: the Lean file is the source byte for byte (SHA-256 `8d6a97209d11a9d8b421192addfcafcd455786f7fee76cf5518e9c8bb80f3821`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
