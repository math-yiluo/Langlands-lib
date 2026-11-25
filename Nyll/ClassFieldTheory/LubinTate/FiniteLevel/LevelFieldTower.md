# The tower of standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` and `π` a uniformizer. The standard Lubin–Tate level `L_n` is generated over `K` by a primitive root chosen independently for each `n` in a fixed separable closure of `K`. The file shows that these fields nevertheless form an increasing tower.

- `standardLubinTatePrimitivePredecessorInLevelField hπ hmn`: for `m ≤ n`, the element `f^(n−m)(λ_n)` of `L_n`, where `λ_n` is the chosen generator and `f` is the standard Lubin–Tate polynomial; in the separable closure it is the polynomial predecessor used by the exact-torsion theorem.
- `standardLubinTateLevelField_mono`: for `m ≤ n`, `L_m ≤ L_n` as intermediate fields of the separable closure.

The predecessor is a root of the primitive polynomial of level `m`, which is irreducible, hence its minimal polynomial. As `L_n/K` is Galois, that polynomial splits in `L_n`, so all its roots in the separable closure, including the chosen generator of `L_m`, lie in `L_n`.

The inclusion is of intermediate fields; it does not say that the chosen generators are compatible (`f^(n−m)(λ_n) = λ_m` is not claimed).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LevelFieldTower.lean`: the Lean file is the source byte for byte (SHA-256 `1ef5e689e087371401e29adfac4052cbf621e0ff62d19d352f1ab49cb601d3a7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
