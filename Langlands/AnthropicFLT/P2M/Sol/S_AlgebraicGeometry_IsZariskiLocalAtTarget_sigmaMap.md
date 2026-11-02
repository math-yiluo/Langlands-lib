# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry` dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Universe generalization: The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. The FLT lemma is stated for coproducts indexed by `σ : Type u` of schemes in universe `u`. The Hilbert scheme is a coproduct over `Polynomial ℚ : Type` of schemes in universe `uz`, so the index type is generalized to `σ : Type*` with `[Small.{u} σ]` (such coproducts exist in `Scheme.{u}`). This generalizes the statement: for `σ : Type u` the instance `Small.{u} σ` holds, giving the FLT statement. The FLT proof used `sigmaMk : (Σ i, X i) ≃ₜ ∐ X`, which Mathlib only provides for `σ : Type u`; it is replaced by an argument with the open cover `sigmaOpenCover` (the ranges of the `Sigma.ι` cover `∐ X`) and the pairwise disjointness of these ranges (`disjoint_opensRange_sigmaι`). The changed lines are:
  - line 25 here:
    FLT text (universe-0 port):

    ```lean
    variable {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)
    ```

    replacement:

    ```lean
    variable {σ : Type*} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)
    ```
  - lines 38–49 here:
    FLT text (universe-0 port):

    ```lean
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
        rw [sigmaMk_mk] at hxy ⊢
    ```

    replacement:

    ```lean
        obtain ⟨i, x, rfl⟩ : ∃ i, ∃ x' : X i, (Limits.Sigma.ι X i) x' = x := by
          have hcov : (⨆ i, (Limits.Sigma.ι X i).opensRange) = ⊤ := by
            have h := (sigmaOpenCover X).iSup_opensRange
            simp only [sigmaOpenCover_f] at h
            exact h
          have hx : x ∈ ((⨆ i, (Limits.Sigma.ι X i).opensRange : (∐ X).Opens) : Set ↥(∐ X)) := by
            rw [hcov]; trivial
          rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx
          obtain ⟨i, hi⟩ := hx
          rw [Scheme.Hom.coe_opensRange] at hi
          obtain ⟨x', hx'⟩ := hi
          exact ⟨i, x', hx'⟩
    ```
  - line 63 here:
    FLT text (universe-0 port):

    ```lean
        {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    ```

    replacement:

    ```lean
        {σ : Type*} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap`. Statement. `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`: for a morphism property `P` local on the target
and a family of morphisms `fᵢ : Xᵢ ⟶ Yᵢ` indexed by a `u`-small type `σ` (in any universe), all
satisfying `P`, the induced morphism of coproducts `∐ Xᵢ ⟶ ∐ Yᵢ` satisfies `P`.

Proof (namespace `AlgebraicGeometry.SigmaMapU4`). `sigmaMap_sigmaι_apply` (the map on points) and
`isPullback_sigmaι_sigmaMap`: each `fⱼ` is the pullback of `∐ f` along the coproduct inclusion of `Yⱼ`.
The inclusions form an open cover of `∐ Yᵢ` (`sigmaOpenCover`), so `P` is checked on the pullbacks
(`IsZariskiLocalAtTarget.of_openCover`), which are isomorphic to the `fⱼ`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry.SigmaMapU4.sigmaMap_sigmaι_apply`
- theorem `P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry.SigmaMapU4.isPullback_sigmaι_sigmaMap`
- theorem `P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
