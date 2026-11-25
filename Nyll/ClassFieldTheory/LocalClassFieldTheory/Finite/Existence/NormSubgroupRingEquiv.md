# Norm subgroups under isomorphisms of field extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `M / F` and `M' / F'` be finite-dimensional field extensions, and let `eF : F ≃+* F'` and `eM : M ≃+* M'` be ring isomorphisms compatible with the algebra maps, that is `algebraMap F' M' ∘ eF = eM ∘ algebraMap F M`. This file shows that field norms, and hence norm subgroups, are carried along.

- `fieldNormHom_map_ringEquiv`: for a unit `y` of `M`, `eF` applied to the norm of `y` from `M` to `F` is the norm of `eM y` from `M'` to `F'`.
- `fieldNormSubgroup_map_ringEquiv`: the image of `fieldNormSubgroup F M` under `eF` on units is exactly `fieldNormSubgroup F' M'`.

The first rests on Mathlib's `Algebra.norm_eq_of_equiv_equiv`; the second follows from it in both directions. The header explains the purpose: transporting finite local class field theory to a small representative. The four fields may live in different universes, and nothing local is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupRingEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `f990760dd34da63e34c93b8903ca002033baba60450f0b276194faaf9672d109`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
