# Construction of the Artin map at a finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, L/K a finite abelian extension, v a finite place of K, and w an extension of the v-adic absolute value to L. This file builds the local Artin homomorphism K_vˣ → Gal(L/K). The library's local reciprocity map for the localized completion L_w/K_v is composed with the identification of Gal(L_w/K_v) with the decomposition group of w in Gal(L/K).

## Main definitions

- Local-field structure on the completion of K for the absolute value `adicAbv K v`. `finitePlaceArtinCompletionValued` and `finitePlaceArtinCompletionValuativeRel` give the valuation induced by the nonarchimedean norm. `finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField` makes the completion an `IsNonarchimedeanLocalField`.
- `finitePlaceLocalArtinInputMonoidHom v`: units of Mathlib's `v.adicCompletion K` → units of that completion, via `finitePlaceCompletionUnitsContinuousMulEquiv`. `finitePlaceCompletionRingEquiv_eq_relative` says two ring isomorphisms between the two completions agree.
- `finitePlaceLocalArtinLocalizedAlgebra`, `finitePlaceLocalArtinFiniteDimensional`, `finitePlaceLocalArtinIsAbelianGalois`: the localized completion at w is a finite abelian extension of the completion of K.
- `finitePlaceLocalArtinMonoidHom v w`: K_vˣ → Gal(L_w/K_v), the library's `Universe.abelianLocalArtinMonoidHom` after the input map.
- `finitePlaceLocalToGlobalMonoidHom v w`: Gal(L_w/K_v) → Gal(L/K), the inverse of `decompositionGroupEquivAlgebraicLocalizationAut` followed by inclusion of the decomposition group.
- `finitePlaceArtinMonoidHomOfExtension v w`: the composite of the two, with factorization lemma `..._factor` (by `rfl`).
- `chosenFinitePlaceArtinMonoidHom v`: the same for the library's chosen extension `chosenFinitePlaceExtension v`.

## Results

- `finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap`: take the chosen element `chosenLocalOrderSection v 1`, whose Mathlib valuation is exp(−1) (a uniformizer). Its image has `valuationMap` value −1 in the local-field structure above. The docstring calls this the inverse-standard normalization.
- Evaluation lemmas write `finitePlaceLocalArtinMonoidHom` and `finitePlaceArtinMonoidHomOfExtension` explicitly in terms of the local Artin map and the decomposition-group isomorphism. The `_universe` forms hold in all universes. The forms without that suffix rewrite to the native `abelianLocalArtinMonoidHom`.

## Points to watch

- The native evaluation lemmas (`finitePlaceLocalArtinMonoidHom_apply`, `..._apply_normalized`, `..._apply_normalized_at`, `finitePlaceArtinMonoidHomOfExtension_apply_normalized`) require K and L in `Type` (universe 0). Only the `_universe` versions are universe-polymorphic.
- Two completions of K at v occur: Mathlib's `adicCompletion` (the source of the maps) and the completion for `adicAbv K v` (where local reciprocity is applied). The input map converts between them.
- The sign of `valuationMap` on a uniformizer is −1, opposite to the usual normalized valuation.
- `chosenFinitePlaceArtinMonoidHom` depends on a chosen place above v. Its independence of that choice is proved in another file of the library.
- `NumberField L` is not assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean`: the Lean file is the source byte for byte (SHA-256 `a785cc29ed1c0feed060bf3137b6f1e5ce7f619e63f21e6ae0ed7e1ea2194b6b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
