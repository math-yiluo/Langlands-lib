# Finite Čech cohomology of a sheaf on an integral closed subscheme, by noetherian induction (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` proper, `K` an ordered affine cover of `V`, and
`Z₀` a nonempty closed subset of `V` whose reduced subscheme is integral, with closed immersion `iZ`.
Assume:

- `hO`: the pushforward `iZ_* 𝒪` of the structure sheaf of the subscheme has finitely generated Čech
  cohomology for `K` (`CechFinite K`);
- `ih` (induction hypothesis): every coherent, quasi-coherent presheaf of modules over `π` supported in a
  closed subset strictly smaller than `Z₀` has finitely generated Čech cohomology for `K`.

Then for every presheaf of modules `H` on the subscheme whose pushforward `iZ_* H` is coherent and
quasi-coherent, `iZ_* H` has finitely generated Čech cohomology for `K`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih` and proves it from `solution`.

## Proof outline

**Auxiliary results** (namespace `…OModulePresheaf.PivotAux`). These are the same as in the generic-freeness
file: preservation of coherence and quasi-coherence by kernels, cokernels, products, powers and
`restrOpen`; `eq_zero_of_res_basicOpen_eq_zero`; `isNoetherian_of_isProper`; coherence and quasi-coherence
of the structure presheaf and of its pushforward along a closed immersion. In addition, `cechFinite_pow`:
finite Čech cohomology passes to `F.pow n`, by induction on `n` using the affine short exact sequences
`0 → F^m → F^{m+1} → F → 0` and the FLT theorem `OModulePresheaf.cechFinite_of_affSES_mid`.

**Main argument.** Write `G = iZ_* H` and `O = iZ_* 𝒪`.

1. By the FLT theorem `OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral` (generic freeness),
   there are an affine open `U₀`, `f ∈ Γ(V, U₀)` with `W₀ = D(f)` meeting `Z₀`, and sections
   `y₁, …, y_r` making `ψ₀ : O^r → G`, `m ↦ ∑ mᵢ yᵢ`, bijective over every affine open inside `W₀`. Put
   `Z₁ = Z₀ \ W₀`, a closed set strictly smaller than `Z₀`.
2. Compare `G` and `O^r` through the fibre product `P = ker δ`, where
   `δ : G × O^r → G|_{W₀}` (`restrOpen W₀`) sends `(x, m)` to `x|_{W₀} − ψ₀(m|_{W₀})`. The projections give
   `α : P → G` and `β : P → O^r`. On every affine open `U` disjoint from `Z₁`, restriction from `U` to
   `U ∩ W₀` is bijective on `G` and on `O^r`, since `iZ⁻¹(U) ⊆ iZ⁻¹(W₀)`. So `α` and `β` are bijective
   there. `P` is coherent and quasi-coherent by the auxiliary results.
3. For a morphism `φ` between coherent quasi-coherent presheaves that is bijective on affine opens disjoint
   from `Z₁`, the kernel and cokernel are supported in `Z₁`, so they have finite Čech cohomology by `ih`
   (`hflk`).
4. `O^r` has finite Čech cohomology (`cechFinite_pow` and `hO`). Applying the FLT theorems
   `cechFinite_of_affSES_left`, `cechFinite_of_affSES_mid` and `cechFinite_of_affSES_right` to the short
   exact sequences `0 → ker β → P → im β → 0`, `0 → im β → O^r → coker β → 0`, `0 → ker α → P → im α → 0` and
   `0 → im α → G → coker α → 0` transfers finiteness from `O^r` to `P` and then to `G`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left`, `…_mid`, `…_right` are renamed
  to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
