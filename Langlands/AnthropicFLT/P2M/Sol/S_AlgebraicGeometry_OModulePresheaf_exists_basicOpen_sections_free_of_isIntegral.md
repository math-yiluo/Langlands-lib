# Generic freeness of a coherent sheaf on an integral closed subscheme (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` proper, and `Z₀` a nonempty closed subset of
`V` whose reduced subscheme `Z₀S` (the subscheme of the vanishing ideal, with closed immersion `iZ`) is
integral. Let `H` be a presheaf of modules on `Z₀S` (over `iZ ≫ π`) whose pushforward `iZ_* H` to `V` is
coherent and quasi-coherent. Then there are an affine open `U₀` of `V` and `f ∈ Γ(V, U₀)` with
`D(f) ∩ Z₀ ≠ ∅`, a number `r` and sections `y₁, …, y_r` of `H` over `iZ⁻¹(U₀)`, such that for every affine
open `W ⊆ D(f)` the map `Γ(Z₀S, iZ⁻¹ W)^r → H(iZ⁻¹ W)`, `m ↦ ∑ mᵢ · yᵢ|_W`, is bijective. So `H` is free of
rank `r` with basis `(yᵢ)` over every affine open inside `D(f)`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral` states this as
`AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral` and proves it from
`solution`.

## Proof outline

**Auxiliary results** (namespace `…OModulePresheaf.GenericFreenessAux`):

- `support_vanishingIdeal'`: the support of the vanishing ideal of `Z` is `Z`;
- coherence and quasi-coherence are preserved by kernels (on locally noetherian `V`), cokernels, finite
  products and powers (`isCoherent_ker`, `isCoherent_coker`, `isQuasicoherent_coker`,
  `isQuasicoherent_ker`, `isCoherent_prod`, `isQuasicoherent_prod`, `isCoherent_pow`,
  `isQuasicoherent_pow`), and quasi-coherence by `restrOpen` when the intersections are affine
  (`isQuasicoherent_restrOpen`);
- `eq_zero_of_res_basicOpen_eq_zero`: for a quasi-coherent `F`, a section over an affine `U` that vanishes
  on every member of a finite cover of `U` by basic opens is zero;
- `isNoetherian_of_isProper`: a scheme proper over a noetherian ring is noetherian;
- `isCoherent_pushforwardUnit`, `isQuasicoherent_unit`, `isQuasicoherent_pushforwardUnit`: the structure
  presheaf is quasi-coherent, and its pushforward along a closed immersion is coherent and quasi-coherent.

**Main argument.**

1. Pick a point of `Z₀` and an affine open `U₀` of `V` containing it. Then
   `A = Γ(Z₀S, iZ⁻¹ U₀)` is a noetherian domain (`Z₀S` is integral and, being proper over `R`,
   noetherian), and `M = H(iZ⁻¹ U₀)` is a finitely generated, hence finitely presented, `A`-module (from
   coherence of `iZ_* H`).
2. Over the fraction field of `A`, the localization of `M` is free of some rank `r`. By
   `Module.FinitePresentation.exists_free_localizedModule_powers` there is `g ≠ 0` in `A` such that `M_g`
   is free of rank `r` over `A_g`. Lift `g` to `f ∈ Γ(V, U₀)` (surjectivity of `iZ` on sections). Then
   `D(f) ∩ Z₀ ≠ ∅` because `g ≠ 0` on the integral scheme `Z₀S`.
3. Choose a basis of `M_g` of the form `yᵢ / 1` (rescaling by units), giving `y₁, …, y_r ∈ M`.
4. For an affine open `W ⊆ D(f)`, cover `W` by finitely many basic opens `D(f'_p)` of `U₀` contained in
   `W`. On each `D(f'_p)`, `H` is the localization of `M` at the image `h_p` of `f'_p`, by
   quasi-coherence. Because `g` becomes a unit there, the map `m ↦ ∑ mᵢ yᵢ` is bijective over `D(f'_p)`
   (`hψbasic`): injectivity and surjectivity are checked by clearing denominators against the basis of
   `M_g`.
5. Glue over `W`. Injectivity follows from `eq_zero_of_res_basicOpen_eq_zero` applied to the pushforward of
   the structure sheaf. For surjectivity, a section `x` over `W` satisfies `(f''_p)^{N_p} x = ∑ m'_p,i yᵢ`
   on each piece (using quasi-coherence of `iZ_* H` and of `𝒪^r`). A partition of unity
   `1 = ∑ c_p (f''_p)^{N_p+1}` in `Γ(V, W)` then writes `x` in the image.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` is renamed
  to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
