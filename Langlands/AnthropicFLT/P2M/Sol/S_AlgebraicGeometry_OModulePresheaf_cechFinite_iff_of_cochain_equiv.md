# Isomorphic Čech complexes have equally finite cohomology (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv`.
Its declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv`.

## Statement

`solution`: let `R` be a commutative ring, `F` a presheaf of modules over `π : V ⟶ Spec R` and `G` one over
`π' : V' ⟶ Spec R`, with ordered affine covers `K` of `V` and `K'` of `V'`. Suppose that `e q` are
`R`-linear isomorphisms between the Čech cochain modules `F.cochain K q ≅ G.cochain K' q` that commute with
the differentials (`e (q+1) (d x) = d (e q x)`). Then `F.CechFinite K ↔ G.CechFinite K'`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv` and proves it from `solution`.

## Proof outline

1. `d_comp_equiv` restates the compatibility as an equation of linear maps, and `map_ker_d` shows that `e q`
   maps cocycles onto cocycles. So `e q` restricts to an isomorphism `kerEquiv` of cocycle modules
   (`kerEquiv_apply_coe`).
2. `map_comap_range`: `kerEquiv (q+1)` maps coboundaries onto coboundaries. So it induces an isomorphism
   `hSuccEquiv` of the cohomology modules `HSucc`.
3. `cechFinite_iff_of_cochainEquiv`: finite generation transfers along these isomorphisms in both
   directions.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
