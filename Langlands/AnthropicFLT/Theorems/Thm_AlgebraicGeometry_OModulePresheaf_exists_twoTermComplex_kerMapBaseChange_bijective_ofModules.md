# A two-term complex of free modules computing the global sections of a line bundle after any base change

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`.

## Statement

`AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`: for a
noetherian ring `R`, a proper flat `f : X ⟶ Spec R`, a locally trivial rank-one `M : X.Modules` (`htriv`) and
an ordered affine cover `𝒰` of `X`, there exist `G : CoherentBaseChange.TwoTermComplex.{u, u} R`,
`ι0 : G.C0 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 0`,
`ι1 : G.C1 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 1` and
`comm : (OModulePresheaf.ofModules f M).d 𝒰 0 ∘ₗ ι0 = ι1 ∘ₗ G.d` such that for every commutative `R`-algebra
`A` the map `TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A` is
bijective. As in FLT, the file removes some instances and simp lemmas for the rest of the file
(`attribute [-instance]` and `attribute [-simp]`); this does not affect the statement.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules.solution R _ _ X f _ _ M htriv 𝒰`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The
theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` and
  `Definitions.Def_AlgebraicGeometry_TwoChartCech` and the corresponding `P2M.Sol` module are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).
