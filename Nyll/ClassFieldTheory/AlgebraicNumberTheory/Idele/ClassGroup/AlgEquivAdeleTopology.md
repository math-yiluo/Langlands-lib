# Continuity of the transport of adeles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields K and M with a ℚ-algebra isomorphism e : K ≃ M, the library transports adeles by a ring isomorphism `adeleCongr e`. This file proves it continuous.

- `continuous_adeleCongr e`: `adeleCongr e` is continuous from the adele ring of K to that of M.

The two factors are treated separately. On the finite adeles, the map is a map of restricted products along the bijection of finite places `finitePlaceCongr e`. Each local map `finitePlaceAdicCompletionCongrHom e W` is continuous and carries local integers into local integers, so `RestrictedProduct.mapAlong_continuous` applies; the identification with `adeleCongr` uses `adeleCongr_finiteComponent`. On the infinite adeles, each coordinate is a continuous completion map at the corresponding infinite place, through `adeleCongr_infiniteComponent`.

The statement concerns the forward map only; the file does not package `adeleCongr e` as a homeomorphism.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivAdeleTopology.lean`: the Lean file is the source byte for byte (SHA-256 `85cfd9bd08261587e79c9a867e4dd6641ba8c9d4841f350f12a1ac13b545df8e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
