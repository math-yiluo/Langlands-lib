# The Čech complex of a line bundle commutes with base change (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial`.

## Statement

`solution`: let `π : X ⟶ Spec R` be separated, `𝒰` an ordered affine cover of `X`, `M : X.Modules` locally
trivial of rank one (`htriv`), and `A` a commutative `R`-algebra. Write `X_A = X ×_{Spec R} Spec A`, with
projections `fst : X_A ⟶ X` and `snd : X_A ⟶ Spec A`, `M_A` for the pullback of `M` along `fst`, and
`𝒰.baseChange π A` for the pulled-back cover (`Def_AlgebraicGeometry_OrderedAffineCoverComap`). Then there are
`A`-linear equivalences `E i : A ⊗[R] Cⁱ(𝒰, M) ≃ₗ[A] Cⁱ(𝒰_A, M_A)` between the base change of the Čech
cochains of `OModulePresheaf.ofModules π M` and the Čech cochains of `OModulePresheaf.ofModules snd M_A`, such
that

- they commute with the differentials: `E (i + 1) ∘ (d i ⊗ A) = d_A i ∘ E i`;
- `E i (a ⊗ c)` at `s` is `a` times the restriction to `(𝒰.baseChange π A).inter s` of the image of `c s`
  under the unit of the pullback–pushforward adjunction for `fst`.

The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial` states this
as `AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial` and proves it from
`solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.CechBaseChange`.

1. **Restrictions** (section `EqRes`). `eqRes` is the restriction along an equality of opens, as a linear
   equivalence, and `res_res_eq_res_res` compares two composites of restrictions.
2. **Affine intersections** (section `Affine`). Since `π` is separated, intersections of affine opens are
   affine (`isAffineOpen_inf_of_isSeparated'`), so every `𝒰.inter s` is affine (`isAffineOpen_inter'`).
3. **One simplex** (section `Main`). `unitAt s` sends a section of `M` over `𝒰.inter s` to the corresponding
   section of `M_A` over `(𝒰.baseChange π A).inter s` (`unit_res` says the adjunction unit commutes with
   restriction). For an affine open, `Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial`
   (from the corresponding theorem module) gives an `A`-linear equivalence `A ⊗[R] Γ(M, U) ≅ Γ(M_A, fst⁻¹ U)`
   extending the unit. Composed with `eqRes` this is `eSimplex s` (`exists_eSimplex`, `eSimplex_one_tmul`,
   `eSimplex_tmul`; `tmul_eq_smul_one_tmul` reduces to `1 ⊗ m`).
4. **Cochains.** `E i` combines the `eSimplex s` over all `i`-indices `s` (a finite product commutes with
   `A ⊗[R] -`), with values `E_tmul`, `E_one_tmul`. Because the unit commutes with restrictions
   (`unitAt_res`), `E` intertwines the differentials on elements `1 ⊗ c` (`E_d_one_tmul`), hence everywhere by
   `A`-linearity (`E_d`). `solution` is `⟨E, E_d, E_tmul⟩`.

As in FLT, the file removes some simp lemmas for the rest of the file (`attribute [-simp]`).

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` and
  `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial` are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. These replacements change no declaration,
  statement or proof step.
