# The norm residue symbol on norms of prime elements

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityPrimeNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L / K` realized inside `SeparableClosure K` by a `K`-embedding `i`, the library has a norm residue symbol `concreteNormResidueSymbolOfEmbedding K L i D v hcf` from `Kˣ` to the abelianization of `Gal(L / K)`, obtained by transporting abstract class-formation reciprocity. This file transports the abstract prime-norm formula: the symbol sends the norm of a prime element from the fixed field of a Frobenius lift to the corresponding Galois automorphism.

## Main result

`concreteNormResidueSymbolOfEmbedding_apply_primeNorm` takes:

- degree data `D`, valuation data `v`, and `hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K)`;
- an element `q` of the abstract extension quotient of the realization `i`;
- a Frobenius element `sigma` of `D.FrobeniusElements` whose restriction is `q` (a positive Frobenius lift, in the docstring's words);
- a prime element `pi`, in the sense of `v.IsPrimeElement`, of the abstract fixed field `S` of `sigma`;
- a unit `x ∈ Kˣ` whose image among the base fixed coefficients equals the abstract relative norm of `pi` from `S` down to the base.

It concludes that the norm residue symbol of `x` is the abelianization class of the `K`-automorphism of `L` that corresponds to `q` under `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`.

## Proof

The abstract formula `DegreeData.finiteReciprocityHom_apply_eq_primeNormClass`, applied with `classFieldAxiom_implies_unramifiedUnitCohomology hcf`, and `abstractReciprocityEquiv_apply_of` give the statement in abstract coordinates. It is then transported through the norm-quotient comparison `finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit` and the identification of the abstract quotient with `Gal(L / K)`.

## Points to watch

- The class field axiom is the hypothesis `hcf`, not proved here; `D` and `v` are arbitrary data of the abstract framework.
- `S`, `pi` and the norm are abstract: `S` is a closed subgroup of the absolute Galois group, `pi` is prime with respect to the valuation data `v`, and the hypothesis on `x` compares it with the class-formation relative norm, not with a field norm from a concrete field.
- No local-field hypothesis on `K` appears; `K` and `L` are in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityPrimeNorm.lean`: the Lean file is the source byte for byte (SHA-256 `034ea24f3415639072f3f3fa0b61a28e162356436c283f889ef2fb493a22b51c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
