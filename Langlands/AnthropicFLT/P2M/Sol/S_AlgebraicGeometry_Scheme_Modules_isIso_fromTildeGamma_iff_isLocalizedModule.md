# A sheaf of modules on an affine scheme is quasi-coherent iff its basic-open restrictions are localizations

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u` and `M` a sheaf of modules on
`Spec R`. The canonical morphism `M.fromTildeΓ`, from the sheaf associated
with the module of global sections `Γ(M)` to `M`, is an isomorphism if and
only if, for every `f ∈ R`, the restriction map `Γ(M, ⊤) → Γ(M, D(f))` is a
localization of `R`-modules at the powers of `f` (`IsLocalizedModule`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

Both directions use that, on the basic open `D(f)`, the component of
`fromTildeΓ` composed with the canonical map
`tilde.toOpen : Γ(M) → Γ(Γ(M)~, D(f))` is the restriction map of `M`
(`Scheme.Modules.toOpen_fromTildeΓ_app`), and that `tilde.toOpen` is a
localization at the powers of `f`.

- If `fromTildeΓ` is an isomorphism, its component on `D(f)` is a linear
  equivalence `e`, and the restriction map is `e ∘ tilde.toOpen`. A
  localization composed with a linear equivalence is a localization
  (`IsLocalizedModule.of_linearEquiv`).
- Conversely, suppose every restriction map `r` is a localization. The
  functor from sheaves of modules on `Spec R` to sheaves on the underlying
  space is fully faithful, so it suffices that the image of `fromTildeΓ` is
  an isomorphism, and by `TopCat.Sheaf.isIso_of_isIso_app_of_isBasis` it
  suffices to check this on the basis of basic opens. On `D(f)`, both
  `tilde.toOpen` and `r` are localizations of `Γ(M)` at the powers of `f`, so
  the universal property gives a linear equivalence `e` with
  `e ∘ tilde.toOpen = r`. The component `g` of `fromTildeΓ` on `D(f)` also
  satisfies `g ∘ tilde.toOpen = r`, so `g = e` by uniqueness
  (`IsLocalizedModule.linearMap_ext`). Hence `g` is bijective, so an
  isomorphism.
