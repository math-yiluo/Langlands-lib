# Finite-place norm kernels of a global Artin map

Module `Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields. This file states, with Mathlib's types, a local–global compatibility of the global Artin map at finite places.

`exists_finiteAbelianGlobalArtin_finitePlaceNormKernel`: there is a surjective homomorphism `artin` from Mathlib's idele class group `NumberField.IdeleClassGroup (𝓞 K) K` onto Gal(L/K) such that, for every finite place `v` of K and every x in K_vˣ, `artin` kills the class of x (`IdeleClassGroup.ofAdicCompletion`) if and only if x lies in `finitePlaceTensorNormSubgroup K L v`, the image of the norm from K_v ⊗_K L.

The map is the library's global norm residue homomorphism, transported to Mathlib's idele class group. On K_vˣ it agrees with a chosen local Artin map, whose kernel is the local norm group, equal to the tensor-norm image.

The statement is existential and fixes only the kernels at finite places: as the file says, values are not yet matched against a separately chosen local Artin map, and real places are not treated.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FinitePlaceLocalGlobalNormKernel.lean`: the Lean file is the source byte for byte (SHA-256 `8faaa5bf856e0e2fe3f32c5724be350f8f2da3f82828207929c49b2f04944569`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
