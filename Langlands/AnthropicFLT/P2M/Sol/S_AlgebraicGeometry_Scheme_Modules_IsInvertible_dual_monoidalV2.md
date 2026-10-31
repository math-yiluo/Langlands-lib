# The dual of an invertible sheaf is invertible and inverse to it

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2` states under its FLT name.

## Statement

Let `X` be a scheme and `L` an invertible sheaf of modules on `X` (the port's
`Scheme.Modules.IsInvertible`: locally isomorphic to the structure sheaf).
Use the monoidal closed structure on `X.Modules` of the FLT modules
`Definitions/Def_SheafOfModules_Monoidal` and `Def_SheafOfModules_MonoidalV2`:
the tensor product is the sheafification of the tensor product of presheaves
of modules, and `Scheme.Modules.dual L` is the internal hom from `L` to the
unit `𝟙_ X.Modules` (the structure sheaf). Then `dual L` is invertible and
`L ⊗ dual L ≅ 𝟙_ X.Modules`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names), `p2m_open_scoped` by `open scoped`; a command left with nothing to open or export is dropped; the `p2m_export` into the root namespace is dropped, since the root names already resolve to the same declarations. No declaration, statement or proof step changed;

## Proof outline

The Lean file contains, in two sections, private copies of the auxiliary
results it uses (among them the proof of `PresheafOfModules.isSheaf_ihomObj`);
these copies come from the FLT source.

1. Presheaf level. For a presheaf of modules `F` on a category, let
   `dual F` be the presheaf internal hom into the unit and
   `ev : F ⊗ dual F ⟶ 𝟙` the evaluation (the uncurrying of the identity). A
   *trivialization below* an object `X₀` (`TrivializationBelow`) is a family
   of sections `gen f ∈ F(Y)`, for all arrows `f : X₀ ⟶ Y` of the opposite
   category, compatible with restriction and such that `a ↦ a • gen f` is
   bijective. Given one, the coordinate maps form a section `dualGen` of
   `dual F` over `X₀` that generates it, and `ev` is bijective at `X₀`, with
   inverse `a ↦ a • (gen ⊗ dualGen)` (`ev_app_bijective`).
2. Local bijectivity. If every object has a covering sieve all of whose
   members carry a trivialization below them, then `ev` is locally injective
   and locally surjective, hence inverted by sheafification (`W_ev`).
3. Invertible sheaves. For `L` invertible, the opens below which `L.val`
   carries a trivialization form a covering sieve of every open
   (`trivSieve_mem`): a trivialization `L|U ≅ 𝒪_U` restricts to smaller opens,
   and its inverse image of `1` gives the generators (`gen₀`). By step 2 and
   `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`,
   sheafification maps `ev` to an isomorphism.
4. The tensor isomorphism. The presheaf `dual L.val` is already a sheaf
   (`PresheafOfModules.isSheaf_ihomObj`, in this port), and `dual L` is by
   construction its sheafification, so `dual L` is isomorphic to it
   (`dualIsoModel`, via the counit `sheafifyCounitIso`). Hence
   `L ⊗ dual L ≅ sheafify (L.val ⊗ dual L.val) ≅ sheafify 𝟙 ≅ 𝟙`, using
   `Scheme.Modules.tensorIsoSheafify`, step 3 and `sheafifyUnitIso`.
5. Invertibility of the dual. On an open `U` where `L|U ≅ 𝒪_U`, the pullback
   along `U.ι` is monoidal (`Functor.Monoidal.μIso`,
   `pullbackTensorUnitObjIso`), so
   `(dual L)|U ≅ 𝒪_U ⊗ (dual L)|U ≅ L|U ⊗ (dual L)|U ≅ (L ⊗ dual L)|U ≅ 𝒪_U`.
