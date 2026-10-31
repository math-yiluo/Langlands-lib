# Čech cohomology of a pushforward along a closed immersion (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R`, `i : Z ⟶ V` a closed immersion, `H` a presheaf
of modules on `Z` (over `i ≫ π`), and `K` an ordered affine cover of `V`. Then the pushforward `i_* H` has
finitely generated Čech cohomology for `K` if and only if `H` has for the preimage cover `K.preimage i` of
`Z`. The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff` states
this as `AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff` and proves it from `solution`.

## Proof outline

1. `resEq` is the `R`-linear isomorphism `H(U) ≅ H(U')` given by restriction when `U = U'` (`resEq_apply`).
   `res_res_apply` composes restrictions.
2. `map_iInf_fin'`: preimages commute with finite intersections, so the intersections of the preimage cover
   are the preimages of the intersections of `K` (`inter_preimage`).
3. `pushforwardCochainEquiv`: the Čech cochains of `H` for `K.preimage i` and of `i_* H` for `K` are
   isomorphic, termwise by `resEq`. `pushforwardCochainEquiv_d`: the isomorphism commutes with the
   differentials.
4. The FLT theorem `OModulePresheaf.cechFinite_iff_of_cochain_equiv` gives the equivalence.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
