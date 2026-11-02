# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 29 here); in 46 lines the replacements `Type` (universe 0) → `Type uz` (26 places), `Scheme.{0}` → `Scheme.{uz}` (24 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization and pieces strengthening): Statement change (strengthening the Hilbert-polynomial pieces clause): the FLT clause `∀ Pℚ, ∃ U : Opens, IsClosed U ∧ QuasiCompact (U.ι ≫ π) ∧ (∀ families, range ⊆ U ↔ Hilbert polynomial Pℚ)` is replaced by `∃ U : Polynomial ℚ → Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧ ∀ Pℚ, IsClosed (U Pℚ) ∧ QuasiCompact ((U Pℚ).ι ≫ π) ∧ (…)`: the pieces form one family of pairwise disjoint opens covering the scheme. This is needed by the task (the relative endomorphism scheme is the disjoint union of its pieces) and implies the FLT clause. The pieces are the ones of the FLT proof (images of the coproduct inclusions, and their preimages in the later stages). In this file the scheme of morphisms is an open subscheme `U` of the Hilbert scheme, and its pieces are the preimages `U.ι ⁻¹ᵁ P Pℚ` of the pieces of the Hilbert scheme. The local lemma `piecesM` now takes one piece `P` of the Hilbert scheme with its properties and proves them for `U.ι ⁻¹ᵁ P` (FLT: it took the whole clause and produced an existential); the main proof applies it to each member of the family and proves pairwise disjointness and covering from those of the Hilbert scheme (`Scheme.Hom.preimage_inf`, `Scheme.Hom.preimage_bot`, `Scheme.Hom.preimage_iSup`, `Scheme.Hom.preimage_top`). The changed lines are:
  - lines 420–423 here:
    FLT text (universe-0 port):

    ```lean
        (hpieces : ∀ Pℚ : Polynomial ℚ, ∃ P : Hilb.Opens, IsClosed (P : Set Hilb) ∧ QuasiCompact (P.ι ≫ πH) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd (fW f g) s))
    ```

    replacement:

    ```lean
        (Pℚ : Polynomial ℚ) (P : Hilb.Opens) (hPc : IsClosed (P : Set Hilb)) (hPqc : QuasiCompact (P.ι ≫ πH))
        (hP :
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{uz}) (ι : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd (fW f g) s))
    ```
  - lines 430–433 here:
    FLT text (universe-0 port):

    ```lean
                    Pℚ.eval (d : ℚ)))
        (Pℚ : Polynomial ℚ) :
        ∃ V : (U : Scheme.{0}).Opens, IsClosed (V : Set (U : Scheme.{0})) ∧ QuasiCompact (V.ι ≫ U.ι ≫ πH) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```

    replacement:

    ```lean
                    Pℚ.eval (d : ℚ))) :
        IsClosed ((U.ι ⁻¹ᵁ P : (U : Scheme.{uz}).Opens) : Set (U : Scheme.{uz})) ∧
          QuasiCompact ((U.ι ⁻¹ᵁ P).ι ≫ U.ι ≫ πH) ∧
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```
  - lines 435–436 here:
    FLT text (universe-0 port):

    ```lean
              (Set.range (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1.base ⊆ (V : Set (U : Scheme.{0})) ↔
                ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
              (Set.range (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1.base ⊆ ((U.ι ⁻¹ᵁ P : (U : Scheme.{uz}).Opens) : Set (U : Scheme.{uz})) ↔
                ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
  - line 440 here:
    FLT text (universe-0 port):

    ```lean
      obtain ⟨P, hPc, hPqc, hP⟩ := hpieces Pℚ
      refine ⟨U.ι ⁻¹ᵁ P, hPc.preimage U.ι.continuous, ?_, ?_⟩
    ```

    replacement:

    ```lean
      refine ⟨hPc.preimage U.ι.continuous, ?_, ?_⟩
    ```
  - lines 497–499 here:
    FLT text (universe-0 port):

    ```lean
          (∀ Pℚ : Polynomial ℚ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```

    replacement:

    ```lean
          (∃ U : Polynomial ℚ → H.Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧
            ∀ Pℚ : Polynomial ℚ, IsClosed (U Pℚ : Set H) ∧ QuasiCompact ((U Pℚ).ι ≫ πH) ∧
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```
  - lines 501–502 here:
    FLT text (universe-0 port):

    ```lean
              (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
                ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
              (Set.range (pt S' s φ hφ).1.base ⊆ (U Pℚ : Set H) ↔
                ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
  - lines 547–553 here:
    FLT text (universe-0 port):

    ```lean
      · exact piecesM f g πH ptH ι𝒵 U huniv hUL 𝓛X 𝓛Y hpieces
    ```

    replacement:

    ```lean
      · obtain ⟨P, hPdisj, hPcov, hP⟩ := hpieces
        refine ⟨fun Pℚ => U.ι ⁻¹ᵁ P Pℚ, fun P₁ P₂ h => ?_, ?_, fun Pℚ =>
          piecesM f g πH ptH ι𝒵 U huniv hUL 𝓛X 𝓛Y Pℚ (P Pℚ) (hP Pℚ).1 (hP Pℚ).2.1 (hP Pℚ).2.2⟩
        · have h' : Disjoint (P P₁) (P P₂) := hPdisj h
          change Disjoint (U.ι ⁻¹ᵁ P P₁) (U.ι ⁻¹ᵁ P P₂)
          rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp h', Scheme.Hom.preimage_bot]
        · rw [← Scheme.Hom.preimage_iSup, hPcov, Scheme.Hom.preimage_top]
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat`. Statement. `AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat` (the scheme of
morphisms): for `f : X ⟶ Spec S` proper, flat, finitely presented and `g : Y ⟶ Spec S` separated, flat, finitely
presented, with invertible `𝓛X`, `𝓛Y` giving closed immersions by sections, there are a scheme `H ⟶ Spec S` and a
natural assignment `pt` of `S`-points of `H` to the morphisms `φ : X ×_S Spec S' ⟶ Y` over `S` (affine tests in
universe `uz`), surjective and injective; `H ⟶ Spec S` is separated and locally of finite presentation; and there
is a family `U P` of pairwise disjoint opens covering `H`, each closed and
quasi-compact over `Spec S`, such that `pt φ` lands in `U P` iff the Hilbert polynomial of
`pr₁^*𝓛X ⊗ φ^*𝓛Y` on `X ×_S Spec S'` (the dimensions of the sections of its powers on the geometric fibres) is `P`.

Proof. Section `Graph`: a morphism `φ` corresponds to its graph, a flat, finitely presented closed subscheme of
`(X ×_S Y) ×_S Spec S'` whose projection to `X ×_S Spec S'` is an isomorphism (`graph`, `isClosedImmersion_graph`,
`flat_graph`, `lfp_graph`, `exists_graph_of_isIso`, `eq_of_iso_graph`). Apply the ported Hilbert scheme
`exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections` to `X ×_S Y` with
`pr₁^*𝓛X ⊗ pr₂^*𝓛Y` (ported `Scheme.Modules.IsInvertible_tensor_monoidalV2`,
`Scheme.Modules.ClosedImmersionBySections_pullback_fst_tensor_pullback_snd`). The universal family
`Z ⊆ X × Y × Hilb` (ported `exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`) has a
projection to `X ×_S Hilb`; `H` is the open locus `U` of `Hilb` over which this projection is an isomorphism (ported
`exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat`, with quasi-compact
inclusion by `exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat`), and a point of `Hilb`
lies in `U` iff its family is a graph (ported `range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre`).
Section `Main`/`Clauses` transfers naturality, surjectivity, injectivity, separatedness and finite presentation from
`Hilb` to `U`. Sections `Transport`/`Pieces` (`piecesM`): the pieces are the preimages
`U ∩ U_Hilb P`; they stay pairwise disjoint and cover `U` (see the changes above), and the Hilbert polynomial of the
graph equals the one computed on `X ×_S Spec S'` with `𝓛X ⊗ φ^*𝓛Y` (ported
`Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase`, `geomFibreH0Finrank_graph`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.fW`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.prX`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.prX_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.prX_snd`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.isSeparated_prX`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph_fst_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph_fst_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph_prX`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.isClosedImmersion_graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.flat_graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.lfp_graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.eq_of_iso_graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.exists_graph_of_isIso`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.bc`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.isPullback_bc`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graph_bc`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.bc_comp_w`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.NatH`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.SurjH`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.InjH`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.UnivZ`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.ULocus`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.mX`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.isPullback_mX`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.prX_comp_mX`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.xH`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.range_xH_subset`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.ptM`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.ptM_ι`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.natM`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.surjM`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.injM`
- abbrev `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.LW`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.graphIso`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.powCongr`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.locIsoOnBase_of_iso`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.geomFibreH0Finrank_graph`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm.piecesM`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre` (same contribution).
Other imports: none.
