# The infinite global Artin map on idele classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K and an abelian Galois extension Ω/K, possibly infinite, this file passes the infinite global Artin homomorphism I_K → Gal(Ω/K) to the idele class group C_K = I_K / K×.

- `infiniteGlobalArtinMonoidHom_principalIdele` (simp): the Artin map kills every principal idele.
- `infiniteGlobalIdeleClassArtinMonoidHom : IdeleClassGroup K →* Gal(Ω/K)`, the induced map on the quotient by `IdeleGroup.principalSubgroup K`. On the class of an idele a it takes the value of the idele Artin map at a (`..._mk`, simp).
- `infiniteGlobalIdeleClassArtinMonoidHom_continuous` and `infiniteGlobalIdeleClassArtinContinuousMonoidHom`: the induced map is continuous for the quotient topology on C_K and the Krull topology.
- `infiniteGlobalIdeleClassArtinContinuousMonoidHom_denseRange`: its image is dense.

Triviality on principal ideles is checked in each coordinate of Mathlib's inverse limit over finite Galois layers, where it is the finite statement `globalArtinMonoidHom_principalIdele`. Continuity and density come from the idele-level map, because the quotient map is a quotient map and is onto.

Only density of the image is shown, not surjectivity onto Gal(Ω/K).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/InfiniteGlobalArtinDescent.lean`: the Lean file is the source byte for byte (SHA-256 `0ad6bfa4688ed7b046253a246a6ce050a2acf873169cbee70762c58dc69b81a1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
