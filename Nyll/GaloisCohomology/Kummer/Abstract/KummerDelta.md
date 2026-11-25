# Abstract finite abelian Kummer theory: the group Delta

Module `Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract setting (closed subgroups `G_L ≤ G_K` of a topological group `G` stand for fields `L ⊇ K`, and `A` is an integral representation of `G` with discrete coefficients and continuous action, the hypothesis `hcontinuous : IsContinuousDiscreteRepresentation A` of the main result), an equivariant operator `wp : A ⟶ A` defines `Delta = wp(A^L) ∩ A^K`, where `A^L` and `A^K` are the elements of `A` fixed by `G_L` and `G_K`, and the radical group `wp⁻¹(Delta)`. The file proves that `L` is exactly the field `K(wp⁻¹(Delta))`.

## Main definitions

- `ambientFixedAddSubgroup A H`: the elements of `A` fixed by the closed subgroup `H`, as an additive subgroup of `A`.
- `kummerDeltaAddSubgroup A wp K L`: `wp(A^L) ∩ A^K`.
- `kummerRadicalAddSubgroup A wp K L`: `wp⁻¹(Delta)`.

## Main results

- `kummerRadical_fixed_of_ker_le_zmultiples`: if `ker wp ⊆ ℤ·xi` with `xi` fixed by `G_K`, every element of `wp⁻¹(Delta)` is fixed by `G_L`.
- `finiteAbelian_kummerRadical_fixingSubgroup_eq`: assume `G_L` is normal in `G_K` with `G_K / G_L` finite, commutative and killed by `n`; let `xi ∈ A` be fixed by `G_K`, of additive order `n`, with `wp xi = 0` and `ker wp ⊆ ℤ·xi`. Then the closed subgroup of `G_K` fixing `wp⁻¹(Delta)` pointwise is `G_L`.

## Proof

The finite abelian assembly theorem (`finiteAbelian_globalOperator_generators`) gives a finite set `S` with `K(S) = L` and `wp(S) ⊆ A^K`; then `S ⊆ wp⁻¹(Delta)`, which gives one inclusion. The other is the first result.

## Points to watch

- The hypothesis `hAxiom : SatisfiesIntegralCyclicNormKernelVanishing A`, defined elsewhere in the library, is a Hilbert-90-type axiom (vanishing of Tate `Ĥ⁻¹` on finite cyclic layers); it is assumed and passed to the assembly theorem.
- The result identifies the field cut out by the radical group; it is not the full Kummer correspondence between subgroups of `Delta` and extensions.
- Fixed modules are additive subgroups of `A`, not the library's representations `A_L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean`: the Lean file is the source byte for byte (SHA-256 `6004f0d41917f2e8cab1e0d958331070eba8064a63f80570e771d23443ec4184`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
