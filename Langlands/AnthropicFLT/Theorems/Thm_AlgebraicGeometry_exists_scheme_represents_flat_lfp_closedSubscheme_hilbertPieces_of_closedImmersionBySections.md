# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.solution S f 𝓛X hX₁ hX₂`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 21 here); in 11 lines the replacements `Type` (universe 0) → `Type uz` (5 places), `Scheme.{0}` → `Scheme.{uz}` (7 places) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization and pieces strengthening): Statement change (strengthening the Hilbert-polynomial pieces clause): the FLT clause `∀ Pℚ, ∃ U : Opens, IsClosed U ∧ QuasiCompact (U.ι ≫ π) ∧ (∀ families, range ⊆ U ↔ Hilbert polynomial Pℚ)` is replaced by `∃ U : Polynomial ℚ → Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧ ∀ Pℚ, IsClosed (U Pℚ) ∧ QuasiCompact ((U Pℚ).ι ≫ π) ∧ (…)`: the pieces form one family of pairwise disjoint opens covering the scheme. This is needed by the task (the relative endomorphism scheme is the disjoint union of its pieces) and implies the FLT clause. The pieces are the ones of the FLT proof (images of the coproduct inclusions, and their preimages in the later stages). The changed lines are:
  - lines 69–72 here:
    FLT text (universe-0 port):

    ```lean
          (∀ Pℚ : Polynomial ℚ, ∃ U : Hilb.Opens, IsClosed (U : Set Hilb) ∧ QuasiCompact (U.ι ≫ πH) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```

    replacement:

    ```lean
          (∃ U : Polynomial ℚ → Hilb.Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧
            ∀ Pℚ : Polynomial ℚ, IsClosed (U Pℚ : Set Hilb) ∧ QuasiCompact ((U Pℚ).ι ≫ πH) ∧
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```
  - lines 74–75 here:
    FLT text (universe-0 port):

    ```lean
              (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set Hilb) ↔
                ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
              (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U Pℚ : Set Hilb) ↔
                ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections` (the
Hilbert scheme): for `f : X ⟶ Spec S` flat and locally of finite presentation with an invertible `𝓛X` giving a
closed immersion by sections, there are a scheme `Hilb ⟶ Spec S` and a natural assignment `pt` of `S`-points of
`Hilb` to the flat, finitely presented closed subschemes of `X ×_S Spec S'` (all commutative rings `S'` in the
universe `uz`), which is surjective and injective up to isomorphism of subschemes; `Hilb ⟶ Spec S` is separated
and locally of finite presentation; and there is a family
`U P` (`P : ℚ[X]`) of pairwise disjoint opens covering `Hilb`, each closed and quasi-compact over `Spec S`, such
that a family lands in `U P` iff its Hilbert polynomial is `P`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections` (same contribution).
Other imports: none.
