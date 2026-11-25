# Norm quotients of fixed fields and the abstract norm-residue symbol

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω` be a separably closed Galois extension of a field `k`. Let `L ≤ K` be closed subgroups of `Gal(Ω/k)`, `K` of finite index and `L` of finite index in `K`, and let `F ⊆ E` be their fixed fields (`abstractFixedField`, `abstractRelativeFixedField`). The class formation is the Galois module of units of `Ω`. The file identifies the cohomological norm quotient of this class formation with the ordinary norm quotient `F^×/N(E^×)`. It also proves two properties of the abstract fixed-field norm-residue symbol: its value on norms of prime elements, and, from this identification, its dependence on norm classes only.

## Main results

- `map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup`: the equivalence between the `K`-fixed units of `Ω` and `F^×` maps the cohomological `finiteNormSubgroup` onto the norm subgroup `N(E^×)` of `F^×`.
- `fixedFieldFiniteNormQuotientEquivNormQuotient`: the resulting additive isomorphism `FiniteNormQuotient ≃+ Additive (NormQuotient F E)`. `fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass` says it sends the finite norm class of a fixed unit to the norm class of the corresponding element of `F^×`.
- `abstractFixedFieldNormResidueSymbol_apply_primeNorm`: take degree data `D`, valuation data `v`, and suppose `L` is normal in `K`. Let `q ∈ K/L`, let `σ` be a Frobenius element whose restriction is `q`, and let `π` be a prime element for `v` at the Frobenius fixed field of `σ`. Then the symbol of the relative norm of `π`, read as a unit of `F`, is the image of `q` in `Gal(E/F)^ab`.
- `abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq`: two units of `F` with the same norm class have the same symbol.
- `fixedFieldQuotientEquiv_mk_compatibility`: for a field `K`, a finite abstract field `H` with fixed field `F`, a finite normal subextension `J`, and an `F`-isomorphism `e` from the separable closure of `F` to that of `K`, conjugation by `e` makes the ambient quotient isomorphism agree with the intrinsic one for the embedding `e⁻¹` of the fixed field of `J`.

## Proofs

The prime-norm formula combines two facts: the finite reciprocity map sends `q` to the norm class of the norm of a prime (`finiteReciprocityHom_apply_eq_primeNormClass`), and the norm-residue symbol inverts it (`normResidueSymbol_finiteReciprocityHom`). The norm-class statement uses injectivity of the norm-quotient isomorphism.

## Points to watch

- The class field axiom for the units of `Ω` is not proved here: it enters the symbol theorems as the hypothesis `hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω)`, and `D`, `v` are arbitrary data.
- In the prime-norm theorem, primality of `π` is the hypothesis `hπ`.
- `finiteNormSubgroup`, `FiniteNormQuotient`, Frobenius elements and the symbol are the library's class-formation notions.
- `k` and `Ω` live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/FixedFieldNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `38f1f03cce922616fc2dadffd2493c98407a6dbee0b84c2e632cd76bfb454eee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
