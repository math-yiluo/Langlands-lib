# Chow's lemma for integral proper schemes over a noetherian ring (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ChowDatum_nonempty`. Its declarations live in
the namespace `P2MW.S_AlgebraicGeometry_ChowDatum_nonempty`.

## Statement

`solution`: let `R` be a noetherian ring, `V` an integral scheme and `π : V ⟶ Spec R` proper. Then
`ChowDatum π` is nonempty. That is (see `Def_AlgebraicGeometry_ProjSpace`), there are a scheme `V'` with a
proper morphism `p : V' ⟶ V`, a closed immersion `ι` of `V'` into a product `ℙ^{e₀}_R ×_R ⋯ ×_R ℙ^{e_{m−1}}_R`
compatible with the structure morphisms, and a dense open `U ⊆ V` over which `p` is an isomorphism. The
theorem module `Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty` states this as
`AlgebraicGeometry.ChowDatum.nonempty` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.ChowLemma`.

1. **Finite affine cover.** `FinAffCover V` is a finite, linearly ordered cover by affine opens.
   `FinAffCover.exists_of_isProper`: one exists, since `V` is quasi-compact.
2. **Charts.** For an affine open `W`, `canonicalAlg π W` is the `R`-algebra structure on `Γ(V, W)`
   (`canonicalAlg_compat`), and `Γ(V, W)` is of finite type over `R` (`gammaFiniteType`). Choose a surjection
   from `R[X₁, …, X_N]` and extend it to `chartφ : R[X₀, …, X_N] → Γ(W, ⊤)` with `X₀ ↦ 1` (`chartN`,
   `chartφ_surj`, `chartφ_X0`). The irrelevant ideal generates the unit ideal (`chartφ_irr`), so `chartφ`
   induces a morphism `chartJ : W ⟶ ℙ^N_R` over `Spec R` (`chartJ_over`) whose image lies in `D₊(X₀)`
   (`chartJ_preimage_D0`). The factorization `chartJD : W ⟶ D₊(X₀)` is a closed immersion (`chartJD_ι`,
   `chartJD_closed`): `D₊(X₀)` is affine and the ring map is surjective.
3. **The datum** (`chowDatum_nonempty`). Discard empty members of the cover and let `U` be the
   intersection of the remaining `m` affines. It is nonempty and dense because `V` is irreducible. The
   charts give `jU : U ⟶ P = ∏ₖ ℙ^{eₖ}_R` (`ProjSpace.prodLift`). The graph `ψ : U ⟶ V ×_R P` is an
   immersion, closed in `U ×_R P` and open in `V ×_R P`. Let `V'` be the scheme-theoretic image of `ψ`,
   with `p : V' ⟶ V` and `ι : V' ⟶ P` the two projections. Then:
   - `p` is proper and surjective, with dense image containing `U`. `V'` is irreducible, reduced (the
     image of a reduced scheme), hence integral, and noetherian.
   - `ι` is proper. On the preimage of each chart `K.U (σ k)` the composite of `ι` with the `k`-th projection
     equals the chart `chartJ` composed with `p` (`h5b`, by agreement on the dense `U` and separatedness).
     The preimage of `D₊(X₀)` under that projection is exactly `p⁻¹(K.U (σ k))` (`h5c`). With the charts
     being monomorphisms, this makes `ι` a monomorphism, hence a closed immersion
     (`IsClosedImmersion.iff_isProper_and_mono`).
   - Over `U`, the section of `p` given by `ψ` is a surjective closed immersion of reduced schemes, hence an
     isomorphism, so `p` is an isomorphism over `U`.

`solution` is `chowDatum_nonempty`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_ChowDatum_nonempty.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and
is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpace` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. `p2m_export "AlgebraicGeometry" "…"` becomes
  `export _root_.AlgebraicGeometry (…)` with the same names. `p2m_open "AlgebraicGeometry"` becomes
  `open _root_.AlgebraicGeometry`. The three `p2m_reactivate` commands become
  `open scoped P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry.ChowLemma`, the last two also
  opening `P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry` scoped. They re-activate the scoped
  instances `FinAffCover.fι` and `FinAffCover.linι` after the namespace closes. No declaration, statement or proof step changed.
