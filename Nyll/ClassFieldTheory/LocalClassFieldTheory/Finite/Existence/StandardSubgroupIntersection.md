# Intersecting the unramified and principal-unit norm conditions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In a nonarchimedean local field `K`, fix `ϖ ∈ Kˣ` of normalized valuation `1`. An element of `⟨ϖ⟩ U_K^n` whose valuation is divisible by `d` lies in `⟨ϖ^d⟩ U_K^n`. This file proves that subgroup calculation and applies it to norm subgroups of composita: the unramified degree-`d` factor contributes the divisibility condition, and a Lubin–Tate factor the principal-unit condition.

## Main results

Here `uniformizerPrincipalSubgroup K ϖ d n` is the standard subgroup `⟨ϖ^d⟩ U_K^n`, and `unramifiedNormSubgroup K d` is the subgroup of elements whose valuation is divisible by `d` (as used through `mem_unramifiedNormSubgroup_iff`).

- `unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le`: if `valuationMap K ϖ = 1`, then `unramifiedNormSubgroup K d ⊓ uniformizerPrincipalSubgroup K ϖ 1 n ≤ uniformizerPrincipalSubgroup K ϖ d n`. Proof: write `x = ϖ^k z` with `z` a principal unit; then `v(x) = k`, so `d ∣ k`.
- `finiteGaloisCompositum_normSubgroup_le_of_standard`: let `U`, `T` be abstract finite Galois subextensions of the absolute Galois group of `K`. Assume, as hypotheses, that the norm subgroup of `U` (transported to `Kˣ`) lies in `unramifiedNormSubgroup K d`, that of `T` lies in `⟨ϖ⟩ U_K^n`, and that a subgroup `H` contains `⟨ϖ^d⟩ U_K^n`. Then the norm subgroup of the compositum `U.compositum T` lies in the image of `H`. The proof uses that the norms of a compositum are norms from each factor.
- `finiteAbelianCompositum_normSubgroup_le_of_standard`: the same statement for finite abelian subextensions.

## Points to watch

- The norm containments for the two factors (`hUle`, `hTle`) are hypotheses here; they are supplied elsewhere for the actual unramified and Lubin–Tate factors.
- The conclusions are containments in abstract class-formation coordinates, stated through `baseUnitsEquivGaloisAmbientFixed`, not in terms of field norms.
- The first lemma allows `K` in any universe; the two composita results take `K : Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`: the Lean file is the source byte for byte (SHA-256 `766f9a5d4ae613106713efd1123066c1874c78c48f47992c43715ef17058cf67`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
