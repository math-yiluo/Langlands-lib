# The absolute Galois group of a finite extension inside that of the base

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F/K` be a finite extension and `e` an `F`-algebra isomorphism from the separable closure of `F` to `K^sep`. Conjugation by `e` identifies `Gal(F^sep/F)` with a closed subgroup of finite index of `Gal(K^sep/K)`. The file builds this identification in two settings: for `F` the fixed field of a finite abstract field `H`, and for `F` given abstractly with a `K`-embedding `i : F →ₐ[K] K^sep`. For nonarchimedean local fields it shows that the identification preserves the normalized degree of the residue data.

## Main definitions and results

- `ambientEmbeddedAbsoluteQuotientFinite`: for `F/K` finite and any `i`, the subgroup `H₀` fixing `i(F)` has finite index in `Gal(K^sep/K)`, stated as finiteness of the quotient of `baseField` by `extensionSubgroup`.
- `intrinsicBase_normalizedDegree_eq_localResidueDegree`: for a nonarchimedean local field `F` and `τ ∈ Gal(F^sep/F)`, the normalized degree given by `localResidueDatum F` is `localResidueDegree F τ`. The residue degree of the whole group is 1.
- `intrinsicBaseEquivAmbientFixedField K H e`: the isomorphism of `Gal(F^sep/F)` with `H` for the fixed field `F` of `H`, `τ ↦ e τ e⁻¹`; `_apply_val` records this formula.
- `intrinsicBase_normalizedDegree_eq_ambientFixedField`: for `K` local and `F` with its spectral local-field structure, the normalized degree of `τ` over `F` equals that of `e τ e⁻¹` over `H` for `localResidueDatum K`. It rests on `localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv`.
- `intrinsicBaseEquivAmbientEmbeddedField K F i e`: for `F/K` finite separable, an isomorphism of `Gal(F^sep/F)` onto `H₀`. It passes through the fixed field `F₀ ≅ F` of `H₀` and an auxiliary isomorphism of the separable closure of `F₀` with `K^sep`.
- `intrinsicBaseEquivAmbientEmbeddedField_apply` and `_apply_val`: the isomorphism is again `τ ↦ e τ e⁻¹` on `K^sep`, so the auxiliary choice drops out.
- `intrinsicBase_normalizedDegree_eq_ambientEmbeddedField`: for `K`, `F` nonarchimedean local fields with the valuation of `F` extending that of `K`, this isomorphism preserves normalized degrees. It rests on `localResidueDegree_eq_normalizedDegree_finiteExtensionEquiv`.

## Points to watch

- The two degree comparisons use different local structures on `F`. The fixed-field version uses the library's spectral-norm structure. The embedded version uses the given structure of `F`, assumed compatible with that of `K`.
- `normalizedDegree`, `localResidueDatum`, `intrinsicAbstractBase` and `FiniteAbstractField` are the library's own class-formation notions.
- The local statements take the fields in `Type`; the purely Galois-theoretic constructions are universe-polymorphic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`: the Lean file is the source byte for byte (SHA-256 `52082da958720c52a295103f0a3ce5be0c98d84e666409abfdb31878fb15e4a3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
