# Continuity of the normalized valuation in the norm topology

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a topological group `G` with degree map `D`, module `A` and valuation `v`, this file proves that the normalized valuation v_K : A_K → ℤ̂ is continuous when A_K carries the norm topology. To this end it builds, for every f > 0, the unramified extension of K of degree f.

## Definitions and results

- `unramifiedDegreeHom D K f hf`: the normalized degree d_K followed by reduction modulo f, a continuous homomorphism from the group of K to ℤ/f; it is surjective. Its kernel `unramifiedDegreeKernelWithin` is closed.
- `unramifiedExtensionOfDegree D K f hf`: the fixed field of that kernel, as a closed subgroup of `G`; `finiteUnramifiedExtension` packages it as a finite Galois extension of K, and `finiteUnramifiedAbelianExtension` as an abelian one, its Galois group being ℤ/f.
- `unramifiedExtensionOfDegree_isUnramified`: the extension is unramified, since the kernel contains the inertia. Its degree and residue degree are f (`finiteUnramifiedExtension_degree`, `finiteUnramifiedExtension_residueDegree`).
- `exists_nsmul_mem_of_valueGroup_mem_nhds`: every neighbourhood of 0 in the value group of `v`, with the topology induced from ℤ̂, contains f·z for all z, for some f > 0.
- `normTopology_valuation_continuous`: for a finite abstract field K, v_K is continuous from the norm topology on A_K (`IsContinuousFromNormTopology`).

## Proof

For a neighbourhood containing all multiples of f, take L the unramified extension of degree f; by the norm–valuation formula, v_K of the norm of a from L to K is f·v_L(a), so the subgroup of norms from A_L, which is open, maps into the neighbourhood. Continuity at 0 then suffices because the norm topology is a group topology.

## Points to watch

The fields K are `FiniteResidueAbstractField D` (or `FiniteAbstractField G`), the library's own notions; the value group carries the subspace topology of ℤ̂, not the discrete one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`: the Lean file is the source byte for byte (SHA-256 `0bfd28ae93c19b8bbb69f75ed4e3542b7c3c749aad522890ab24bffb21980dde`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
