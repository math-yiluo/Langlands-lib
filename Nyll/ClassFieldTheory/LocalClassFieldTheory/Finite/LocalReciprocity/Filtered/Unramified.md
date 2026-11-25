# The Artin filtration of an unramified extension is trivial

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `L / K` a finite abelian extension, where `L` carries the structure of a nonarchimedean local field with a valuation extending that of `K`, and is unramified for it (`IsUnramifiedValuedExtension K L`). Both fields are in universe `0`.

- `abelianLocalArtinMonoidHom_integerUnits_eq_one_of_unramifiedValuation`: every unit of `𝒪_K` has trivial image under the local Artin map `abelianLocalArtinMonoidHom K L`. Proof: for such extensions the Artin map sends `x` to `Frob ^ v(x)` (`localArtinMonoidHom_eq_frobenius_zpow`), and units have valuation `0`.
- `artinPrincipalUnitGroup_eq_bot_of_unramifiedValuation`: for every `n`, the Artin image of `U_K^(n)` is trivial.
- `artinPrincipalUnitStepGroup_eq_bot_of_unramifiedValuation`: the real-indexed step filtration is trivial at every real `t`.

The unramified hypothesis is a typeclass on a given valuation of `L`, together with a uniform structure on `L` making it a uniform additive group (`[UniformSpace L] [IsUniformAddGroup L]`); the results hold for every `n`, including `n = 0`, where `U_K^(0)` is the full unit group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Unramified.lean`: the Lean file is the source byte for byte (SHA-256 `437773311a6cfc5570f6c1d10b4c74a0154e2b92ccc4e82b568a4b7acfa0c67f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
