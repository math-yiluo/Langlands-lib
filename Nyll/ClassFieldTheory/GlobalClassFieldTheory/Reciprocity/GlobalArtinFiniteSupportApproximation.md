# Finite-support reduction for the global Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinFiniteSupportApproximation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields. Only finitely many finite-place Artin factors of an idele a of K are nontrivial. The file replaces a by the idele that keeps all its infinite components and exactly those finite components, and shows that the two differ by a relative idele norm, so that the global Artin map and the norm-class map agree on them.

## Main definitions and results

- `globalArtinFiniteSupport a`: the finite set of finite places v at which `chosenFinitePlaceArtinMonoidHom v` of the v-component of a is nontrivial (`mem_globalArtinFiniteSupport_iff`).
- `artinFiniteSupportApproximation a`: the product of the one-place ideles carrying the infinite components of a and its finite components on that support. Simp lemmas: it has the same infinite components as a, the same finite components on the support, and component 1 at the other finite places.
- `artinFiniteSupportApproximation_remainder_mem_relativeIdeleNorm_range`: a times the inverse of its approximation lies in the image of the relative idele norm `RelativeIdeleGroup.norm K L`.
- `globalNormClassFromIdele_relativeIdeleNorm_eq_one` (simp): the map from I_K to C_K modulo idele-class norms kills relative idele norms; this one does not need L/K abelian.
- `globalArtinMonoidHom_eq_artinFiniteSupportApproximation` and `globalNormClassFromIdele_eq_artinFiniteSupportApproximation`: the global Artin map, and the norm-class map, take the same value on a and on its approximation.
- `artinFiniteSupportIdeleClassIsMulCommutative`: commutativity of the idele class group, used as a local instance.

## Proof

The remainder has component 1 at the infinite places and on the support. At any other finite place the Artin factor of a is trivial, so by the local kernel theorem `chosenFinitePlaceArtinMonoidHom_ker` its component is a local norm. The imported characterization `ClassFieldAxiom.relativeIdeleNorm_range_eq_allPlaceLocalNormCondition` (an idele is a relative norm exactly when it is a local norm at every place) then gives the claim. Both maps are trivial on relative norms, which yields the last two statements.

## Points to watch

- The key step rests on that imported characterization of relative idele norms; at an infinite place v, the local norm condition is for the norm from `v.Completion ⊗[K] L`.
- Relative norms are taken in the library's `RelativeIdeleGroup K L`, which is related to `IdeleGroup L` by a base-change equivalence (`relativeIdeleBaseChangeMulEquiv`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalArtinFiniteSupportApproximation.lean`: the Lean file is the source byte for byte (SHA-256 `25610e5f1face88f7084536879a8ca80c1dc3db49e37bae01ba19e58f611b2bb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
