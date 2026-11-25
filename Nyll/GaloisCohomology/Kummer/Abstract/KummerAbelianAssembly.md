# Abstract finite abelian Kummer theory: assembling cyclic radicals

Module `Nyll.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The setting is abstract: `G` is a topological group, "fields" are closed subgroups (`K` stands for `G_K`, `L` for `G_L ≤ G_K`), and `A` is an integral representation of `G` with discrete coefficients and continuous action (`IsContinuousDiscreteRepresentation A`). `A_M` denotes the `G_M`-invariants of `A`, a representation of `G_K / G_M` (`extensionFixedRepresentation`), and `K(S)` is the closed subgroup of `G_K` fixing a set `S ⊆ A` pointwise (`closedSetFixingSubgroup`). The file goes from cyclic layers to a finite abelian layer: radicals built in cyclic subextensions together generate `L` over `K`.

## Main results

- `extensionFixedRepresentation_val_fixed_iff_mem`: if `a ∈ A_M` has trivial stabilizer in `G_K / G_M`, then `k ∈ G_K` fixes `a` in `A` exactly when `k ∈ G_M`.
- `closedSetFixingSubgroup_range_extensionFixed_eq`: given a family of closed subgroups `M_i ≤ G_K`, each normal in `G_K`, elements `a_i` of the `M_i`-invariants of `A` with trivial stabilizers, and `⋂ M_i = G_L`, the subgroup of `G_K` fixing all `a_i` is `G_L`.
- `finiteAbelian_globalOperator_generators`: assume `G_L` is normal in `G_K` with `G_K / G_L` finite, commutative and of exponent dividing `n`; let `wp : A ⟶ A` be an equivariant endomorphism and `xi ∈ A` an element of additive order `n`, fixed by `G_K`, with `wp xi = 0`. Then there is a finite `S ⊆ A` such that `wp(s)` is fixed by `G_K` for all `s ∈ S` and `K(S) = L`.

Two further lemmas unfold membership in `extensionSubgroup` and the quotient action on `A_M`; another says that quotient-fixedness of the descended operator means `wp(a)` is fixed by `G_K` in `A`.

## Proof

`G_K / G_L` is split into cyclic coordinates whose kernels meet trivially (library file on cyclic factors); each coordinate gives a closed intermediate `M_i` with cyclic quotient. The cyclic single-radical theorem (`cyclicGlobalOperator_singleRadical`) gives `a_i` in the `M_i`-invariants of `A` with trivial stabilizer and `wp(a_i)` fixed; the lemma above then yields `K(S) = L` for `S = {a_i}`.

## Points to watch

- The hypothesis `hAxiom : SatisfiesIntegralCyclicNormKernelVanishing A`, defined elsewhere in the library, is a Hilbert-90-type axiom: it is used (through the cyclic step) to obtain the vanishing of Tate `Ĥ⁻¹` of `A_M` for finite cyclic layers. It is assumed, not proved.
- Only one direction of the Kummer correspondence is treated: generation of `L` by radicals. The exact description of the radical group is in the companion file on `Delta`.
- "Fields" are closed subgroups of an abstract group, not Mathlib fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`: the Lean file is the source byte for byte (SHA-256 `0e3976f054d5015af5dd331c7c374c05f0d57cd57569a3a113831ba73de0f37e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
