# Finite Galois extensions of an abstract field

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the library's abstract class field theory, a field is a closed subgroup of a group `G` with a topology, and an extension `L/K` corresponds to an inclusion `G_L ≤ G_K`. This file packages the finite Galois extensions of a fixed `K`, which index the norm topology. It also defines base change, the trivial extension and composita, and compares norm subgroups.

## Definitions

- `FiniteGaloisSubextension K`: a closed subgroup `G_L ≤ G_K` that is normal in `G_K` with finite quotient. It is determined by its subgroup (`ext`).
- `extensionQuotient`: the quotient `G(L/K) = G_K / G_L` as a named type, with its group and finiteness instances. It comes with the projection `extensionQuotientMk` (surjective) and an induction principle `extensionQuotient_inductionOn`.
- Forgetful maps: `toGaloisSubextension` forgets finiteness, `toFiniteAbstractExtension` forgets normality, and `toFiniteAbstractFieldExtension` applies when `K` is finite over the base.
- `IsUnramified` and `IsTotallyRamified` for a degree datum `D`. `isUnramified_iff_inertia_le` states that unramified means `G_K ∩ ker(deg) ≤ G_L`. `isTotallyRamified_iff_image_le` states that totally ramified means the degree image of `G_K` is contained in that of `G_L`.
- `baseChange M L`: for an intermediate `L` with `G_L ≤ G_K`, the extension of `L` given by `G_L ∩ G_M`.
- `refl K`: the trivial extension `K/K`.
- `compositum L₁ L₂`: the extension given by the intersection of the subgroups of `L₁` and `L₂`. It is commutative in its arguments (`compositum_comm`) and lies above both factors (`compositum_le_left`, `compositum_le_right`).

## Results

- Finiteness in towers:
  - `finite_extension_trans`: finiteness is transitive.
  - `finite_extension_over_intermediate`: a finite extension stays finite over any intermediate field.
  - `finite_intermediate_extension`: an intermediate field is finite over the base, without any normality hypothesis.
- `finiteNormSubgroup_compositum_le_left` and `finiteNormSubgroup_compositum_le_right`: the norm subgroup of the compositum `L₁L₂` over `K` is contained in the norm subgroups of `L₁` and of `L₂`. The proof uses transitivity of norms in a tower.

## Watch for

- Fields are represented contravariantly: a larger field has a smaller subgroup, and the compositum is an intersection of subgroups.
- "Unramified" and "totally ramified" are the library's structural notions, defined through the degree map of `D`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `ab82b9bab04eabca85da0297f1393cc3925d7cf4c1064556e748e9e06e5143dd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
