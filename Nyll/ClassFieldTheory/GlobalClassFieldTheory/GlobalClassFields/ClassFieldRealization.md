# Finite abelian subextensions realized as field extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω / k` be a Galois extension and `K` a closed subgroup of `Gal(Ω/k)`. In the abstract class-formation lattice, a finite abelian subextension over `K` (`FiniteAbelianSubextension K`) is given by nested closed subgroups. This file shows that the corresponding fixed fields form a finite abelian Galois extension.

- `IsAbelianGalois.of_base_equiv`: given `e : K ≃+* K'` compatible with the scalar maps into `L`, with `L / K` Galois and `L / K'` abelian Galois, `L / K` is abelian Galois. The Galois hypothesis must be supplied separately.
- `finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional`: the fixed field of the lower subgroup of `L` is finite-dimensional over the fixed field of `K`. It assumes `hKfinite`, finiteness of a quotient of the base-field subgroup by the subgroup attached to `K`.
- `finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois`: this extension is abelian Galois. Its Galois group is isomorphic to the abstract extension quotient, and commutativity is transported through that isomorphism.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClassFieldRealization.lean`: the Lean file is the source byte for byte (SHA-256 `496c2205640741ce70829b2c5fd21971ea2ae9c43c28d4ce28ccdea815e7d0b2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
