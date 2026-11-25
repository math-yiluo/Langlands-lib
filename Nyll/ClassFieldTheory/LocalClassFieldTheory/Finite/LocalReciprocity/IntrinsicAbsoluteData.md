# Absolute Galois data of a field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For any field `F`, this file packages, from the chosen separable closure, the data the abstract class formation needs: the absolute Galois group, its integral representation on the units of the separable closure, and its base subgroup.

- `intrinsicAbsoluteGalois F`: `Gal(SeparableClosure F / F)`.
- `intrinsicAbsoluteUnits F`: the `ℤ`-representation of this group on `(SeparableClosure F)ˣ`.
- `intrinsicAbstractBase F`: the base, given as the closed subgroup fixing the bottom intermediate field.
- `intrinsicAbstractBaseEquivAbsolute`: this subgroup is isomorphic to the whole absolute Galois group, by the identity on underlying automorphisms (`intrinsicAbstractBaseEquivAbsolute_symm_apply_val`).
- `intrinsicFiniteAbstractBase F`: the base as a finite abstract field; `intrinsicFiniteAbstractBase_eq_base` says it equals the class formation's distinguished base `FiniteAbstractField.base`.

The base is written as a fixing subgroup rather than as `⊤` so that it matches subgroups attached to intermediate fields; the equality with the distinguished base is a propositional, not definitional, identification.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`: the Lean file is the source byte for byte (SHA-256 `98ccc0d48a377f00998a006e54f62b7311004938c596fa24554da33960d2217c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
