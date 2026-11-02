# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 16 here); in 8 lines the replacements `Type` (universe 0) → `Type uz` (4 places), `Scheme.{0}` → `Scheme.{uz}` (7 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT proof applies `P2mWs41DescTriple.descend_triple` with the noetherian base `A₀ := ℤ`, which must lie in the universe of `A`. For `A : Type uz` it is applied with `A₀ := ⊥`, the smallest `ℤ`-subalgebra of `A` (the image of `ℤ`), which is noetherian as a quotient of `ℤ` and of finite type over `ℤ`. The finitely generated `⊥`-subalgebra `T` obtained is then of finite type over `ℤ` (transitivity), and `T.restrictScalars ℤ` is the required finitely generated `ℤ`-subalgebra; the remaining data are passed through. The statement only changes by the universe generalization. The changed lines are:
  - lines 168–188 here:
    FLT text (universe-0 port):

    ```lean
            h ≫ πX = πZ ≫ h₀ :=
      P2mWs41DescTriple.descend_triple (A₀ := ℤ) p q h w
    ```

    replacement:

    ```lean
            h ≫ πX = πZ ≫ h₀ := by
      -- universe-generalized port: descend over the image `⊥` of `ℤ` in `A` (a ring in the universe
      -- of `A`), then restrict scalars to `ℤ`
      haveI : IsNoetherianRing (⊥ : Subalgebra ℤ A) := by
        refine isNoetherianRing_of_surjective ℤ (⊥ : Subalgebra ℤ A) (algebraMap ℤ (⊥ : Subalgebra ℤ A)) ?_
        rintro ⟨x, hx⟩
        obtain ⟨n, rfl⟩ := Algebra.mem_bot.mp hx
        exact ⟨n, Subtype.ext rfl⟩
      obtain ⟨T, hT, Z₀, X₀, p₀, q₀, h₀, πZ, πX, H⟩ :=
        P2mWs41DescTriple.descend_triple (A₀ := (⊥ : Subalgebra ℤ A)) p q h w
      haveI : Algebra.FiniteType (⊥ : Subalgebra ℤ A) ↥T := (Subalgebra.fg_iff_finiteType _).mp hT
      haveI : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ A) := by
        refine ⟨⟨∅, ?_⟩⟩
        rw [Finset.coe_empty, Algebra.adjoin_empty]
        exact (Algebra.eq_top_iff).mpr fun x => by
          obtain ⟨y, hy⟩ := x
          obtain ⟨n, rfl⟩ := Algebra.mem_bot.mp hy
          exact ⟨n, Subtype.ext rfl⟩
      have hFT : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans (S := (⊥ : Subalgebra ℤ A))
        inferInstance inferInstance
      exact ⟨T.restrictScalars ℤ, (Subalgebra.fg_iff_finiteType _).mpr hFT, Z₀, X₀, p₀, q₀, h₀, πZ, πX, H⟩
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation`. Statement. `AlgebraicGeometry.exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation`:
for a ring `A` (universe `uz`) and a morphism `h : Z ⟶ X` over `Spec A` between proper, flat, finitely presented
schemes, there is a finitely generated subring `T ⊆ A` (subalgebra over `ℤ`) with proper, flat, finitely presented
models `Z₀`, `X₀` over `Spec T` and a model `h₀ : Z₀ ⟶ X₀` of `h`, all base-changing to the given data.

Proof. The descent is performed over the subring `A₀ = ⊥` (the image of `ℤ` in `A`, a quotient of `ℤ`, hence
noetherian and of finite type over `ℤ`) instead of over `ℤ` itself (see the changes above: this avoids a
universe mismatch between `ℤ` and `A`). The ported
`exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation` gives models
of `Z` and `X` over a finitely generated `A₀`-subalgebra, and the ported
`exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation` descends `h` after a further
enlargement; finally the `A₀`-subalgebra is viewed as a subalgebra over `ℤ` (`restrictScalars`), still finitely
generated.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.P2mWs41DescTriple.isPullback_lift_of_fac`
- lemma `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.P2mWs41DescTriple.specMap_algebraMap_comp`
- lemma `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.P2mWs41DescTriple.package`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.P2mWs41DescTriple.descend_triple`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation` (Library, ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`).
Other imports: `Mathlib`.
