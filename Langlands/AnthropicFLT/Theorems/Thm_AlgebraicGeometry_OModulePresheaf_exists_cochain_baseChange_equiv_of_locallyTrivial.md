# The Čech complex of a line bundle commutes with base change

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial`.

## Statement

`AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial`: for a separated
`π : X ⟶ Spec R`, an ordered affine cover `𝒰` of `X`, a locally trivial rank-one `M : X.Modules` (`htriv`) and
a commutative `R`-algebra `A`, there are `A`-linear equivalences
`E i : A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A] (OModulePresheaf.ofModules (pullback.snd π (specMap R A)) ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj M)).cochain (𝒰.baseChange π A) i`
that commute with the Čech differentials (after base change of the source differential to `A`) and send
`a ⊗ c` at an index `s` to `a` times the restriction of the adjunction-unit image of `c s`. As in FLT, the
file removes some simp lemmas for the rest of the file (`attribute [-simp]`); this does not affect the
statement.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.solution R _ X π _ 𝒰 M htriv A _ _`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` and
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` and the corresponding `P2M.Sol` module are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).
