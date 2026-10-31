# Ordered affine covers and Čech cohomology of presheaves of modules

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`, in namespace
`AlgebraicGeometry`. All objects live in a fixed universe `u`.

## Definitions

**Ordered affine covers.** For a scheme `V`, a `Scheme.OrderedAffineCover V` is a finite, linearly
ordered index type `ι` together with opens `U i` of `V` that are affine (`isAffineOpen`) and cover `V`
(`⨆ i, U i = ⊤`). For such a cover `K`:

- `K.Idx i` is the type of strictly increasing maps `Fin (i + 1) → ι`, that is, of index tuples
  `i₀ < i₁ < ⋯ < iᵢ`. It is finite and has decidable equality.
- `K.inter s` is the intersection `⋂ⱼ U (s j)` of the opens indexed by `s`.
- `K.face s j` deletes the `j`-th entry of `s : K.Idx (i + 1)`: it is `s ∘ Fin.succAbove j`.
- `ofAffine V`, for affine `V`, is the cover with one index whose open is `⊤`.
- `TwoAffineOpenCover.toOrderedAffineCover` turns a cover by two affine opens `U0`, `U1` into the
  ordered cover indexed by `Fin 2` (lifted to universe `u`) with `U 0 = U0` and `U 1 = U1`.

**Presheaves of modules over a base ring.** Let `π : V ⟶ Spec R` for a commutative ring `R`. An
`OModulePresheaf π` assigns to every open `U` of `V` an abelian group `obj U` that is a module over `R`
and over `Γ(V, U)`, compatibly with the `R`-algebra structure on `Γ(V, U)` induced by `π`
(`IsScalarTower R Γ(V, U) (obj U)`). It has `R`-linear restriction maps `res h : obj U' → obj U` for
`h : U ≤ U'` with `res h (a • x) = (a|U) • res h x`, `res` of `U ≤ U` the identity, and
`res (h.trans h') = res h ∘ res h'`. So it is a presheaf of `𝒪_V`-modules with `R`-linear
restrictions, written out by hand.

**Čech complex.** For `F : OModulePresheaf π` and an ordered affine cover `K`:

- `F.cochain K i` is the product of `F.obj (K.inter s)` over all `s : K.Idx i`;
- `F.d K i : F.cochain K i → F.cochain K (i + 1)` is the `R`-linear Čech differential
  `(d c)(s) = ∑_{j=0}^{i+1} (-1)^j · res (c (K.face s j))`;
- `F.H0 K` is the kernel of `F.d K 0`, and `F.HSucc K i` is the quotient of the kernel of
  `F.d K (i + 1)` by the image of `F.d K i`. So `H0` and `HSucc i` are the Čech cohomology modules
  `Ȟ⁰` and `Ȟ^{i+1}` of `F` for the cover `K`;
- `F.CechFinite K` means that `F.H0 K` and every `F.HSucc K i` are finitely generated `R`-modules.

**Finiteness and support conditions.**

- `F.IsCoherent`: for every affine open `U`, `F.obj U` is a finitely generated `Γ(V, U)`-module.
- `F.IsQuasicoherent`: for every affine open `U` and `f ∈ Γ(V, U)`, (a) for every
  `x ∈ F.obj (V.basicOpen f)` there are `n` and `y ∈ F.obj U` with `res y = (f|D(f))ⁿ • x`, and (b) every
  `y ∈ F.obj U` whose restriction to `D(f)` vanishes satisfies `fⁿ • y = 0` for some `n`. Together these
  say that `F.obj (D(f))` is the localization of `F.obj U` at `f`.
- `F.SupportedIn Y`, for a closed subset `Y` of `V`: `F.obj U` is trivial (a subsingleton) for every
  affine open `U` disjoint from `Y`.

**Examples and two-chart data.**

- `unit π` is the structure presheaf: `obj U = Γ(V, U)`, the `R`-module structure comes from `π`, and the
  restrictions are those of the structure sheaf.
- For a cover `𝒱` of `V` by two affine opens, `F.twoChartSections 𝒱` is the datum
  `TwoChartCech.Sections` with `M0 = F.obj U0`, `M1 = F.obj U1`, `M01 = F.obj (U0 ⊓ U1)` and the two
  restriction maps to `U0 ⊓ U1`.

The remaining declarations are unfolding lemmas for these definitions (`face_val`, `inter_le`,
`inter_le_inter_face`, `ofAffine_U`, `toOrderedAffineCover_ι`, `toOrderedAffineCover_U_zero`,
`toOrderedAffineCover_U_one`, `toOrderedAffineCover_U`, `res_refl_apply`, `res_res`, `d_apply`,
`cechFinite_iff`, `isCoherent_iff`, `isQuasicoherent_iff`, `supportedIn_iff`, `unit_obj`,
`unit_res_apply`, `unit_smul`, `unit_algebraMap_smul`, `twoChartSections_M0`, `twoChartSections_M1`,
`twoChartSections_M01`, `twoChartSections_r0_apply`, `twoChartSections_r1_apply`), each proved by `rfl`
or a one-line rewrite.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
