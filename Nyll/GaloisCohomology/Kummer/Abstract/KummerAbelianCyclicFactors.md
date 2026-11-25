# Cyclic factors of a finite abelian layer

Module `Nyll.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For abstract finite abelian Kummer theory, a finite abelian layer `G_K / G_L` is reduced to cyclic layers. The file supplies the group theory, then realizes the cyclic pieces as closed intermediate subgroups of a topological group `G`.

## Group theory

- `finiteCommGroup_exists_jointlyFaithful_cyclic_factors`: a finite commutative group `Q` has finitely many surjections `f_i : Q → ℤ/m_i` (each `m_i > 1`, index type in `Type 0`) whose kernels intersect trivially. It comes from Mathlib's decomposition of `Q` as a product of `ZMod` groups.
- `cyclicFactorSubgroup H f`: for `H` normal in `P` and `f : P ⧸ H →* C`, the kernel of `P → P ⧸ H → C`. It is normal, contains `H`, and its quotient is cyclic (resp. finite) when `f` is surjective and `C` is cyclic (resp. finite).
- `iInf_cyclicFactorSubgroup_eq`: if the `f_i` have trivially intersecting kernels, the pulled-back subgroups intersect in `H`.

## Closed intermediate subgroups

For closed subgroups `L ≤ K` of a topological group `G`, with `G_L` normal in `G_K` and `G_K / G_L` finite:

- `extensionSubgroup_isClosed` and `cyclicFactorSubgroup_isClosed`: `G_L` is closed in `G_K`, and so is each pulled-back kernel, since the finite quotient is discrete.
- `closedCyclicFactorSubgroup`: the pulled-back kernel as a closed subgroup of `G`; it lies between `G_L` and `G_K` (`le_closedCyclicFactorSubgroup`, `closedCyclicFactorSubgroup_le_base`).
- `extensionSubgroup_closedCyclicFactorSubgroup_eq`: seen inside `G_K`, it is the pulled-back kernel; hence it is normal, and its quotient is finite and cyclic when the coordinate is surjective onto a finite cyclic group, and is killed by `n` whenever `G_K / G_L` is.

No radicals or generation statements appear in this file; closedness of the intermediate subgroups uses the finiteness of `G_K / G_L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean`: the Lean file is the source byte for byte (SHA-256 `df52741460367d87ab518a5eaba8c7f3c57063018d04c5e5bba6b90c3b26a600`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
