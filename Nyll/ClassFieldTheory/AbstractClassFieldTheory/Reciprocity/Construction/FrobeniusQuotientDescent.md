# The action of G(L̃ | K) on A_L̃ and descent to K

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusQuotientDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory with a group `G`, a `G`-module `A` (written additively) and a degree map `D`, the quotient `G_K / I_L = G(L̃ | K)` acts on the invariants `A_L̃` of the maximal unramified extension `L̃` of `L`. This file packages that action as a representation, proves telescoping identities for the Frobenius power sums `a + φ a + … + φⁿ⁻¹ a`, shows that the norm `N(L̃|K̃)` kills the degree-zero terms of the equation used in the universal norm-descent lemma, and proves a descent criterion from `A_K̃` to `A_K`. Throughout, `L ≤ K` are closed subgroups with `G_L` normal in `G_K`; the last three results take `K` a finite residue abstract field for `D`.

## Main definitions and results

- `frobeniusQuotientAction_coe_out`: the action of `q` is the action of its representative `Quotient.out q`.
- `frobeniusQuotientActionLinearMap` and `frobeniusQuotientRepresentation`: the action as `ℤ`-linear maps and as a `Rep ℤ (G_K / I_L)` on `A_L̃`.
- `birkhoffSum_eq_frobeniusPowerSum`, `frobeniusPowerSum_add` (splitting `n + m` terms), `frobeniusPowerSum_action_sub` (`φ S − S = φⁿ a − a` for `S` the power sum of `a`), `frobeniusPowerSum_sub_universalNormDescent` (additivity in `a`), and `frobeniusPowerSum_eq_nsmul_of_fixed` (if `q a = a` the sum is `n a`).
- `maximalUnramifiedNorm_frobeniusQuotientAction`: for `L | K` finite, the norm `N(L̃|K̃)`, followed by inclusion back into `A_L̃`, commutes with the action.
- `frobeniusQuotientAction_fixed_of_degreeZero`: a class of normalized degree zero fixes the image of `A_K̃`.
- `maximalUnramifiedNorm_fixed_of_hstar`: for `L | K` finite, if `φ u − u = Σᵢ (τᵢ uᵢ − uᵢ)` in `A_L̃` with each `τ i` of normalized degree zero (hypothesis `hstar`), then `N(L̃|K̃)(u)` is fixed by `φ`.
- `descend_maximalUnramified_fixed_of_finiteSupport`: let `φ` be a Frobenius element of exponent one, `P` a finite Galois intermediate field of `L̃ | K`, and `a ∈ A_K̃` whose image in `A_L̃` comes from `A_P` and is fixed by `φ`. Then `a` comes from `A_K`.

## Proofs

The telescoping identities are instances of general facts on Birkhoff sums of an iterated map. For the descent, every element `k` of `G_K` agrees, modulo `G_P`, with a lift `t` of a Frobenius element of `G(P̃ | K)` of some degree `n` (surjectivity of Frobenius restriction); `t` differs from a power `fⁿ` of a lift of `φ` by an inertia element, which fixes `a` since `a ∈ A_K̃`. Hence `k` fixes `a`.

## Watch for

- `hstar` is a hypothesis: the theorem derives the consequence of the equation, not the equation.
- The descent theorem needs the "finite support" hypothesis that `a` is defined over a finite Galois intermediate field `P`; it assumes no topology on `G` beyond a topological group structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean`: the Lean file is the source byte for byte (SHA-256 `b14c434ee7341295bd9a8c2f4f0c134911b54216db0b86d9650eba0e4f4d9644`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
