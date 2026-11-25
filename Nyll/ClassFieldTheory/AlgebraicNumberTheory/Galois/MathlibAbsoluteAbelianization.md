# Mathlib's abelianized absolute Galois group and the separable model

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For any field K, Mathlib defines the absolute Galois group as Gal(K̄/K) for its algebraic closure, while the library also works with Gal(K^sep/K) for `SeparableClosure K`. This file compares the two abelianizations.

- `absoluteGaloisGroupAbelianizationEquivSeparable K`: an isomorphism of topological groups from `Field.absoluteGaloisGroupAbelianization K` to the topological abelianization of Gal(K^sep/K).
- `absoluteGaloisGroupAbelianizationEquivSeparable_mk` (simp): it sends the class of σ to the class of its restriction to the separable closure.

It is induced, through `topologicalAbelianizationCongr`, by the continuous isomorphism given by restriction to the separable closure (`separableClosureContinuousMulEquiv`), both defined elsewhere in the library.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/MathlibAbsoluteAbelianization.lean`: the Lean file is the source byte for byte (SHA-256 `aa7200e573c0c0a92acfa68080b415ebbca7dbddea1820e5d7bed05210784fac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
