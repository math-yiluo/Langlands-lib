# The local reciprocity law for finite Galois extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of nonarchimedean local fields, this file obtains the reciprocity isomorphism `Gal(L/K)ᵃᵇ ≃ Kˣ / N(Lˣ)` by feeding the residue degree datum `localResidueDatum K`, the valuation `localHenselianValuation K` and the class field axiom `separableClosureUnits_isClassFormation K` into the abstract reciprocity theorem, with the units of `SeparableClosure K` as coefficients.

- `abelianizationEquivNormQuotient K L`: the isomorphism `Abelianization (Gal(L/K)) ≃* NormQuotient K L`.
- `localArtinMonoidHom K L`: the norm-residue symbol `Kˣ → Gal(L/K)ᵃᵇ`, the inverse of reciprocity after the quotient map.
- `localArtinMonoidHom_eq_of_embedding`: the symbol equals the one built from any embedding `L →ₐ[K] SeparableClosure K`; the definition uses one fixed embedding, and the reciprocity isomorphism does not depend on it.
- `localArtinMonoidHom_surjective` and `localArtinMonoidHom_ker`: the symbol is surjective with kernel the norm subgroup `localNormSubgroup K L`.

The class field axiom used here is a theorem of the library, not a hypothesis. Only `L` finite Galois over `K` is assumed; the abelian case is not singled out. The fields `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean`: the Lean file is the source byte for byte (SHA-256 `66832375948d49497aaa6f81dfd60183b8338f74abd4601c96c3ece5c7dea077`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
