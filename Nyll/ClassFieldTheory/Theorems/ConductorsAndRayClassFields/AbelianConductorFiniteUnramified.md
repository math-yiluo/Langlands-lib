# The conductor exponent vanishes exactly at unramified places

Module `Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an abelian extension of number fields and `c` a ray class modulus of K that is the abelian conductor of L/K (`IsAbelianConductor K L c`, the library's notion).

`IsAbelianConductor.finiteExponent_eq_zero_iff_unramified`: for a finite place `v` of K, the exponent of `c` at `v` is zero if and only if every prime `W` of 𝓞_L lying over `v` is unramified over 𝓞_K, in the sense of Mathlib's `Algebra.IsUnramifiedAt`.

The proof identifies `c` with the conductor of the idele-class norm group, by uniqueness of the abelian conductor (`IsAbelianConductor.unique`). The support of the finite part of that conductor is known to be the set of finite places of K that ramify in L, and the statement is a rewriting of membership in that set.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `78b1cf557033d67e89ce2303c9b2ea7e203bef56d151fdb9838b6e31a11e7f81`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
