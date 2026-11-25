# Norm–restriction compatibility of finite-place Artin maps

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.NormRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields, and let K', L' be number fields completing a square: K → K' → L' and K → L → L' are scalar towers and L'/K' is finite abelian Galois. For a finite place W of K' above a finite place v of K, the file shows that the finite-place Artin maps at W and at v are compatible with the norm from the completion K'_W to K_v and with restriction of automorphisms from L' to L.

## Main results

- `finitePlaceNormCompletion F v` and `finitePlaceNormLocalizedCompletion F M v w`: abbreviations for the completion of F under the adic absolute value of v, and for the library's localized completion of M at an extension w of that absolute value.
- `finitePlaceLocalArtinMonoidHom_norm_restriction`: given `hW : finitePlaceBelow W = v`, extensions w of v to L and w' of W to L', and a hypothesis `hcentres` saying that the place of L below the centre of w' is the centre of w, for every unit x of `W.adicCompletion K'` the cross-local restriction (`finitePlaceCrossLocalRestrictionMonoidHom`) of the local Artin image of x equals the local Artin image of the norm of x in `(v.adicCompletion K)ˣ`.
- `finitePlaceArtinMonoidHomOfExtension_norm_restriction`: the same with values in the global Galois groups: restriction Gal(L'/K') → Gal(L/K) composed with `finitePlaceArtinMonoidHomOfExtension` at (W, w') equals `finitePlaceArtinMonoidHomOfExtension` at (v, w) composed with the norm.
- `chosenFinitePlaceArtinMonoidHom_norm_restriction`: for any finite place W of K', with v the place below it, restriction ∘ `chosenFinitePlaceArtinMonoidHom` at W equals `chosenFinitePlaceArtinMonoidHom` at v ∘ norm. The variant `chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq` takes v and `hW` explicitly.

## Proof

The adic completions are identified with the absolute-value completions, and the norm is transported along these ring isomorphisms. After checking that the valuation of K_v extends to that of K'_W and that K'_W/K_v is finite and separable (local compactness, characteristic zero), the local statement follows from the local theorem `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_norm_restriction`. The global forms factor the Artin map through the local-to-global map and use `finitePlaceCrossDecompositionTransport`; the chosen version builds w from the centre of the chosen extension of W and replaces it by the chosen extension of v using `finitePlaceArtinMonoidHomOfExtension_eq`.

## Points to watch

- The algebra structure from `v.adicCompletion K` to `W.adicCompletion K'` is not an instance: each statement installs it by `let` (the `_of_below_eq` variant by `letI`) from `finitePlaceAdicCompletionMap`, and the norm is the library's `LocalFieldTheory.normUnits` for that algebra.
- The extension-level statements carry `hcentres`, a compatibility between the chosen places of L and L'; only the chosen versions discharge it.
- L is not assumed to be a number field; the statements derive this from finiteness over K, except `finitePlaceLocalArtinMonoidHom_norm_restriction`, which takes `[NumberField L]`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/NormRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `47111353352ce43e80d60df026597a69865475b0aee57890f78035cad7c30e90`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
