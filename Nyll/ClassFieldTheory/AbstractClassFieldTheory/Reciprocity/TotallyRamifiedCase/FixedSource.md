# The fixed element in the cyclic totally ramified case

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a compact, Hausdorff, totally disconnected group `G` (module `A` written additively, valuation `v`), this file produces, from a norm equation in a cyclic totally ramified extension L/K, an element of valuation k in an auxiliary field. It is the step before the conclusion k = 0 of the reciprocity argument.

## Definitions and results

- `abstractReciprocity_fixedCombination_of_commute`: in a ℤ-representation of any group, if g and t commute, t fixes c, g and t agree on b, and b − c = g·a − a, then b + a − t·a is fixed by g.
- `FiniteCyclicSubextension.toFiniteGaloisSubextension` forgets the chosen generator; `galoisGenerator` transports the generator to the Galois quotient, and it still generates (`galoisGenerator_generates`).
- `relativeCosetAction_lowerInclusionHom`: the action of G(M/M') on A_M agrees with that of its image in G(M/K).
- `abstractReciprocity_cyclicTotallyRamified_fixedSource`: assume the class field axiom `hcf`, K a finite abstract field (`K : FiniteAbstractField G`), L/K finite cyclic and totally ramified, σ the chosen Frobenius lift of degree one of the generator with fixed field Σ, π_Σ ∈ A_Σ, π_L a prime element of L, w a unit of L and k ∈ ℕ such that k π_L + w and k π_Σ have the same norm to K. Let M be the auxiliary finite Galois extension `abstractReciprocityTotallyRamifiedFiniteGaloisExtension` and M₀ its maximal unramified subextension over K. Then some M₀-fixed element x of `A` has normalized valuation k in M.

## Proof

M contains L and Σ and is unramified over L, so π_L stays prime in M and w stays a unit. The norm identities for elements of L and of Σ (the norm from M to M₀ of such an element is its norm to K, read among the M₀-fixed elements) turn the hypothesis into equal norms from M to M₀; the class field axiom (`abstractReciprocity_exists_hMinusOne_primitive`) gives a with g·a − a = w − u for a generator g of G(M/M₀). With t the Frobenius element in M, which fixes π_Σ, agrees with g on L and commutes with g, the combination lemma makes b + a − t·a fixed by g, hence an M₀-fixed element, of valuation k.

## Points to watch

Unlike the version in `Reciprocity.TotallyRamified`, the action and norm identities are not hypotheses here: they come from results about the auxiliary field M in the files `FrobeniusNorms` and `RestrictionEquiv`. The valuation is computed in M, not in L.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`: the Lean file is the source byte for byte (SHA-256 `bddffe1fa1750fc8986289aa6555a2b611949d048222e22d27faceccc37b2f2d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
