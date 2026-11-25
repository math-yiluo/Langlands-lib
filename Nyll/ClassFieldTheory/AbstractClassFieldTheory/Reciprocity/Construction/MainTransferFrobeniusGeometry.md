# Subgroups and orbit sets for transfer and norm

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Group-theoretic preparation for the compatibility of the reciprocity map with the transfer, in the abstract class field theory of the library. Fields are closed subgroups of `G`, so a tower `K ⊆ K' ⊆ L` appears as `G(L) ≤ G(K') ≤ G(K)`. Here `L/K` is normal and `K'/K` is finite with finite residue structure. The file places `G(L̃/K')` inside `G(L̃/K)` (the quotients by inertia) as a subgroup `H`, records its properties, and matches the transfer index set with the norm index set.

## Main definitions and results

- `transferNormNaturalityIntermediateAbsoluteEquiv`: `G(K')` is isomorphic to its copy inside `G(K)`.
- `transferNormNaturality_intermediateExtension_normal`: if `L/K` is normal, so is `L/K'`.
- `transferNormNaturalityFrobeniusTowerMap_injective`: the map `G(L̃/K') → G(L̃/K)` is injective. Its image `transferNormNaturalityFrobeniusIntermediateSubgroup` (the subgroup `H`) is also the image of `G(K')` under the projection (`..._eq_map`).
- `transferNormNaturalityFrobeniusIntermediateFiniteIndex`: `H` has finite index, without assuming `K'/K` normal. `transferNormNaturalityFrobeniusIntermediate_isClosed`: `H` is closed when `G` is compact and Hausdorff.
- `transferNormNaturalityExtensionRestriction_surjective`, `..._ker_le_intermediate`: restriction `G(L̃/K) → G(L/K)` is surjective, and its kernel lies in `H`.
- `frobeniusFixedCosetClosureEquiv_equivariant`: the identification of `G(K)/G(Σ)` with `G(L̃/K)/Γ`, where `Σ` is the fixed field and `Γ` the closed cyclic subgroup of a Frobenius element `σ`, intertwines the actions of `G(K')` and `H`.
- `transferNormNaturalityTransferNormOrbitEquiv`: for `G` compact and Hausdorff, a bijection between the transfer index set `⟨σ⟩ \ G(L̃/K) / H` and the norm index set `G(K') \ G(K) / G(Σ)`. By `transferNormNaturalityTransferNormOrbitEquiv_mk` and `_apply`, it sends the class of `k` to the class of `k⁻¹`.

## Proofs

The orbit bijection is a composite of equivalences built elsewhere. Inverting double cosets swaps the two sides (`orbitQuotientSwapEquiv`), and passing from `⟨σ⟩` to its closure `Γ` uses that `H` is closed of finite index (`orbitQuotientClosedCyclicEquiv`). The equivariant identification above then transports the orbits along the surjection `G(K') → H`.

## Watch for

The orbit sets are quotients of actions by left multiplication on left cosets, and the bijection involves inversion. A transfer representative `t` therefore corresponds to the norm coset of `t⁻¹`, not of `t`.

The results on `H` and the orbit bijection take normality of `L/K'` as a separate instance hypothesis `hL'normal`, which `transferNormNaturality_intermediateExtension_normal` supplies from normality of `L/K`; they also assume that `G` is a topological group (`IsTopologicalGroup G`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobeniusGeometry.lean`: the Lean file is the source byte for byte (SHA-256 `5aea74989639f1fe3d2463e1431134e45b0667a62560e1e3b31d7889b01043fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
