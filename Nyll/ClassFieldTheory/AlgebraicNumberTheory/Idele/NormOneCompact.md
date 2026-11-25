# Compactness of the norm-one idele classes

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file proves that the norm-one subgroup of the idele class group (ideles modulo principal ideles) is compact. It builds an explicit compact set of norm-one ideles and shows that its image in the idele class group is exactly that subgroup.

## Main results

- `FiniteIdeleGroup.isCompact_integralSubgroup`: the finite ideles that are units at every finite place form a compact set. It is the image of the product of the compact local unit groups.
- `InfiniteIdeleGroup.annulus B`: the archimedean ideles with exp(−B) ≤ ‖a_w‖ ≤ exp(B) at every infinite place w. It is compact (`isCompact_annulus`). The archimedean norm is continuous (`continuous_archimedeanNorm`).
- `InfiniteIdeleGroup.logNorm`: the vector of the numbers m_w·log‖a_w‖, indexed by the infinite places other than the place w₀ omitted in Dirichlet's unit theorem. On units of 𝓞 K it is Mathlib's `logEmbedding` (`logNorm_principalRingUnit`).
- `mem_annulus_of_logNorm_le`: if the archimedean norm of a is 1 and `‖logNorm a‖ ≤ r`, then a lies in the annulus with B equal to the number of infinite places times r.
- `exists_ringUnit_logNorm_le`: every archimedean idele can be multiplied by a unit of 𝓞 K so that its log vector has norm at most `logFundamentalBound`, the sum of the norms of the vectors of a ℤ-basis of the unit lattice, taken as a real basis of the log space (`unitLatticeRealBasis`).
- `IdeleGroup.compactIntegralNormOneSet`: the ideles in such an annulus, integral at all finite places, with archimedean norm 1. The set is compact. By `exists_compactIntegralNormOneSet_representative`, every norm-one idele that is integral at all finite places has the same class modulo principal ideles as an element of this set.
- `normOneIdealClassRepresentative`: one chosen norm-one idele in each ideal class that contains one. `exists_integral_normOne_reduction`: dividing a norm-one idele by the representative of its ideal class and by a principal idele makes it integral at all finite places.
- `compactNormOneClassCover`: the product of the two sets above. It is compact and consists of norm-one ideles.
- `IdeleClassGroup.image_compactNormOneClassCover`: its image in the idele class group is exactly `normOneSubgroup`.
- `IdeleClassGroup.normOneSubgroup_isCompact` and the instance `normOneSubgroupCompactSpace`: the norm-one idele classes form a compact set.

## Proof

The proof combines compactness of the local unit groups, Dirichlet's unit theorem in Mathlib's form (the unit lattice is a full lattice in the log space), finiteness of the class group, and the imported fact that principal ideles have norm one (`principalSubgroup_le_normOneSubgroup`).

## Points to watch

- The norm is the library's `IdeleGroup.absoluteNorm`, the reciprocal of the usual ∏_v |a_v|_v. Its kernel is the usual norm-one subgroup.
- The idele class group carries the quotient topology, and compactness is proved for that topology.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormOneCompact.lean`: the Lean file is the source byte for byte (SHA-256 `0d4a211ed5871d22738e57db3a639db09a03ba3119b4c2b5ef931bc932e701de`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
