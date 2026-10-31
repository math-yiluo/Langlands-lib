# The cokernel of a morphism of quasi-coherent presheaves of modules is quasi-coherent (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker`.

## Statement

`solution`: for `π : V ⟶ Spec R`, presheaves of modules `F, G` over `π` and a morphism `φ : F ⟶ G`
(`OModulePresheaf.Hom`), if `G` and `F` are quasi-coherent then so is the cokernel `OModulePresheaf.coker φ`
(`Def_AlgebraicGeometry_OModulePresheafConstructions`, `Def_AlgebraicGeometry_OrderedAffineCoverCech`). The
theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker` states this as
`AlgebraicGeometry.OModulePresheaf.isQuasicoherent_coker` and proves it from `solution`.

## Proof outline

The proof is `isQuasicoherent_coker` in the namespace `…AlgebraicGeometry.OModulePresheaf.G4T`. Fix an affine
open `U` and `f ∈ Γ(V, U)`.

1. **Lifting** (condition (a)). A class over `D(f)` is represented by `x₀ ∈ G.obj (D(f))`; condition (a) for
   `G` gives `n` and `y ∈ G.obj U` with `y|_{D(f)} = fⁿ • x₀`, and the class of `y` works.
2. **Annihilation** (condition (b)). If the class of `y₀ ∈ G.obj U` vanishes on `D(f)`, then
   `y₀|_{D(f)} = φ(z)` for some `z ∈ F.obj (D(f))`. Condition (a) for `F` gives `w ∈ F.obj U` with
   `w|_{D(f)} = fⁿ • z`, so `fⁿ • y₀ − φ(w)` restricts to `0` on `D(f)` (naturality of `φ`). Condition (b) for
   `G` gives `m` with `fᵐ • (fⁿ • y₀ − φ(w)) = 0`, so `f^{m+n} • y₀ = φ(fᵐ • w)` lies in the image of `φ`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.
