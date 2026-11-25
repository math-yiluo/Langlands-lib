# Abstract capitulation from Witt's transfer theorem

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.AbstractCapitulation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file supplies the group-theoretic and class-formation input for the principal ideal theorem. Let M/K be a finite Galois layer of a profinite group. Let F be the fixed field of the commutator subgroup of Gal(M/K), the largest abelian subextension of M/K. The transfer Gal(M/K)^ab → Gal(M/F)^ab is trivial. In a class formation, the inclusion of norm quotients from K to F is therefore zero.

## Main results

- `transferIntermediateSubgroup_eq_galoisCorrespondenceSubgroup`: let S be a subgroup of Gal(M/K). The transfer construction realizes Gal(M/M^S) as a subgroup of Gal(M/K). This subgroup is exactly S, not only a copy isomorphic to it.
- `commutatorIntermediateTransfer_eq_one`: for S the commutator subgroup, the transfer `transferNormNaturalityTransfer` that enters transfer–norm naturality is trivial.
- `intermediateNormQuotientInclusion_commutator_eq_zero`: setting: an abstract class formation over a compact, Hausdorff, totally disconnected group Γ, with degree data `D`, a Γ-module `A`, valuation data `v`, and `hcf : SatisfiesClassFieldAxiom A`. For a finite Galois subextension M of a finite abstract field K, the map induced by inclusion, from the finite norm quotient of K to that of the fixed field of the commutator subgroup, is zero.

## Proof

The first result is a direct comparison of the two subgroups. The second moves the transfer along this equality and applies Witt's theorem: for a finitely generated group with finite abelianization, the transfer to the commutator subgroup is trivial (`GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization`); the group Gal(M/K) here is finite. The third uses naturality of the norm-residue symbol: on norm quotients, inclusion corresponds to transfer on Galois groups. The transfer is trivial and the norm-residue symbol of M over F is injective, so the inclusion vanishes.

## Points to watch

- The capitulation statement takes the class field axiom as the hypothesis `hcf`. It holds only for class formations that satisfy it.
- The result concerns norm quotients of an abstract class formation, not ideal classes. As the file says, it assumes no realization by actual fields and no equality of norm subgroups. Passing to ideal classes and number fields is left to other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/AbstractCapitulation.lean`: the Lean file is the source byte for byte (SHA-256 `475d4532ce2502abbd8bb4b576a046c916fed0e83e7459c5d85b9c02c0c5bf1f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
