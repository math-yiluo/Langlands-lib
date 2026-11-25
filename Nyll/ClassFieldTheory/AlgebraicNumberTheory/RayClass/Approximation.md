# Multiplicative weak approximation for ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, this file proves the multiplicative form of weak approximation needed for ray class groups. Given an idele `a` and open subgroups `U_v ≤ K_vˣ` at finitely many finite places, there is a single `x ∈ Kˣ` with `a_v x⁻¹ ∈ U_v` at each of these places; open subgroups can also be prescribed at all archimedean places at the same time.

## Main definitions and results

- `IdeleGroup.modulusOfFinset S`: the modulus with exponent `1` at the finite places of `S` and no infinite part; its finite support is `S`.
- `IdeleGroup.exists_principal_quotient_mem_openLocalSubgroups`: for a modulus `m`, an idele `a`, and open subgroups `U_v` at the finite places in the support of `m`, some `x ∈ Kˣ` satisfies `a_v x⁻¹ ∈ U_v` for all such `v`. The `_finset` version takes a finite set of places instead of a modulus.
- `IdeleGroup.exists_principal_quotient_mem_openAllLocalSubgroups`: the same, with open subgroups `V_w` prescribed in addition at every archimedean place `w`, and `a_w x⁻¹ ∈ V_w`; also in a `_finset` version.
- `IdeleGroup.finiteIdeleOfFinset` and `IdeleGroup.ideleOfFiniteLocalFamily`: the (finite) idele with prescribed components on a finite set `S` of finite places and `1` elsewhere.
- `IdeleGroup.principalLocalQuotientMap S U`: the diagonal homomorphism from `Kˣ` to the product over `v ∈ S` of the quotients `K_vˣ / U_v`; `principalLocalQuotientMap_surjective` shows it is onto when every `U_v` is open.

## Proof

The cosets `a_v U_v` (and, at archimedean places, the cosets `a_w V_w`, or all of `K_wˣ` in the first version) form a nonempty open subset of the product of the completions at the support of `m` and at all archimedean places. An imported density result for the diagonal embedding of `K` in that product gives `x ∈ K` in this open set. Since `x` lands in a unit coset at an archimedean place, `x ≠ 0`. Surjectivity of the quotient map applies the finite-set version to an idele built from chosen lifts.

## Points to watch

- Only finitely many finite places are constrained, and the subgroups must be open; this is weak approximation, not a strong approximation statement.
- The density of `K` in the product of completions is not proved here but taken from the ray class development.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Approximation.lean`: the Lean file is the source byte for byte (SHA-256 `abe077c94c905329339469d06cf9987e639a695f453daa5db39076abd552f29f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
