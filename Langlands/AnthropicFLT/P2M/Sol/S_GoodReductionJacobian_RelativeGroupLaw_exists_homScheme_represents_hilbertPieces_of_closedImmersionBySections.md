# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 25 here); in 50 lines the replacements `Type` (universe 0) → `Type uz` (31 places), `Scheme.{0}` → `Scheme.{uz}` (23 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization and pieces strengthening): Statement change (strengthening the Hilbert-polynomial pieces clause): the FLT clause `∀ Pℚ, ∃ U : Opens, IsClosed U ∧ QuasiCompact (U.ι ≫ π) ∧ (∀ families, range ⊆ U ↔ Hilbert polynomial Pℚ)` is replaced by `∃ U : Polynomial ℚ → Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧ ∀ Pℚ, IsClosed (U Pℚ) ∧ QuasiCompact ((U Pℚ).ι ≫ π) ∧ (…)`: the pieces form one family of pairwise disjoint opens covering the scheme. This is needed by the task (the relative endomorphism scheme is the disjoint union of its pieces) and implies the FLT clause. The pieces are the ones of the FLT proof (images of the coproduct inclusions, and their preimages in the later stages). In this file the Hom scheme is a closed subscheme `j : Z ⟶ M` of the scheme of morphisms, and its pieces are the preimages `j ⁻¹ᵁ P Pℚ`. The local lemma `HomSchemeAsm.piecesH` now takes one piece `U` of `M` with its properties and proves them for `j ⁻¹ᵁ U` (FLT: it took the whole clause and produced an existential); the main proof applies it to each member of the family and proves pairwise disjointness and covering from those of `M` (`Scheme.Hom.preimage_inf`, `Scheme.Hom.preimage_bot`, `Scheme.Hom.preimage_iSup`, `Scheme.Hom.preimage_top`). The changed lines are:
  - lines 406–408 here:
    FLT text (universe-0 port):

    ```lean
        (hpieces : ∀ Pℚ : Polynomial ℚ, ∃ U : M.Opens, IsClosed (U : Set M) ∧ QuasiCompact (U.ι ≫ πM) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```

    replacement:

    ```lean
        (Pℚ : Polynomial ℚ) (U : M.Opens) (hUc : IsClosed (U : Set M)) (hUqc : QuasiCompact (U.ι ≫ πM))
        (hU' :
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```
  - lines 414–416 here:
    FLT text (universe-0 port):

    ```lean
                      (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ)))
        (Pℚ : Polynomial ℚ) :
        ∃ U : Z.Opens, IsClosed (U : Set Z) ∧ QuasiCompact (U.ι ≫ j ≫ πM) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```

    replacement:

    ```lean
                      (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ))) :
        IsClosed ((j ⁻¹ᵁ U : Z.Opens) : Set Z) ∧ QuasiCompact ((j ⁻¹ᵁ U).ι ≫ j ≫ πM) ∧
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    ```
  - lines 419–420 here:
    FLT text (universe-0 port):

    ```lean
              (Set.range (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1.base ⊆ (U : Set Z) ↔
                ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
              (Set.range (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1.base ⊆ ((j ⁻¹ᵁ U : Z.Opens) : Set Z) ↔
                ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
  - line 424 here:
    FLT text (universe-0 port):

    ```lean
      obtain ⟨U, hUc, hUqc, hU'⟩ := hpieces Pℚ
      refine ⟨j ⁻¹ᵁ U, hUc.preimage j.continuous, ?_, ?_⟩
    ```

    replacement:

    ```lean
      refine ⟨hUc.preimage j.continuous, ?_, ?_⟩
    ```
  - lines 494–496 here:
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
  - lines 503–504 here:
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
  - lines 530–537 here:
    FLT text (universe-0 port):

    ```lean
      · exact HomSchemeAsm.piecesH LA LB hAc hBc hA hB πM ptM Φ j hZ hU 𝓛A 𝓛B hpieces
    ```

    replacement:

    ```lean
      · obtain ⟨P, hPdisj, hPcov, hP⟩ := hpieces
        refine ⟨fun Pℚ => j ⁻¹ᵁ P Pℚ, fun P₁ P₂ h => ?_, ?_, fun Pℚ =>
          HomSchemeAsm.piecesH LA LB hAc hBc hA hB πM ptM Φ j hZ hU 𝓛A 𝓛B Pℚ (P Pℚ) (hP Pℚ).1 (hP Pℚ).2.1
            (hP Pℚ).2.2⟩
        · have h' : Disjoint (P P₁) (P P₂) := hPdisj h
          change Disjoint (j ⁻¹ᵁ P P₁) (j ⁻¹ᵁ P P₂)
          rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp h', Scheme.Hom.preimage_bot]
        · rw [← Scheme.Hom.preimage_iSup, hPcov, Scheme.Hom.preimage_top]
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`. Statement. `GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections` (the
Hom scheme): let `A ⟶ Spec S` and `B ⟶ Spec S` be commutative group schemes with the abelian-scheme property bundle,
with invertible `𝓛A`, `𝓛B` giving closed immersions by sections. There are a scheme `H ⟶ Spec S` and a natural
assignment `pt` of `S`-points of `H` to morphisms `φ : A ×_S Spec S' ⟶ B` over `S` (affine tests in universe `uz`)
such that every point comes from a homomorphism and `pt` is injective on homomorphisms; `H ⟶ Spec S` is separated,
locally of finite type, locally of finite presentation and formally unramified; and there is a family `U P` of
pairwise disjoint opens covering `H`, each closed and quasi-compact over `Spec S`, such that for a homomorphism `φ`,
`pt φ` lands in `U P` iff the Hilbert polynomial of `pr₁^*𝓛A ⊗ φ^*𝓛B` on `A ×_S Spec S'` (the dimensions of the sections of its powers on the geometric fibres) is `P`.

Proof. Let `M` be the scheme of morphisms from the ported
`exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat`, with universal morphism `Φ` from the
ported `exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point`. By the ported
`RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle`, a morphism is a homomorphism iff
it sends the unit to the unit. So `H` is the locus in `M` where the two morphisms `uM`, `vM : M ⟶ B` (the value of
`Φ` at the unit section, and the unit of `B`) agree: a closed subscheme `j : H ⟶ M`, locally of finite presentation
since `B` is separated and of finite type (ported
`exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated`). Sections `Retr`, `BC`, `Mor`
handle the retraction of points along the unit section and base change. Section `Clauses`: naturality, surjectivity
onto homomorphisms and injectivity are inherited from `M` (`natH`, `surjH`, `injH`); `H` is formally unramified
(`unramH`) by the ported `formallyUnramified_of_forall_specMap_comp_eq_imp_eq`, since homomorphisms agreeing on a
nilpotent thickening are equal (ported `RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker`).
The pieces are the preimages `j⁻¹(U_M P)`; they stay pairwise disjoint and cover `H` (`piecesH`; see the changes
above).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.IsHom`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.eA`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.eA_fst`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.eA_snd`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.isHom_iff`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.compHom`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.comp_inv`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.inv_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.mul_inv_self`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.asPt`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.cst`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.retr`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.retr_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.eA_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.eA_comp_retr`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.retr_eq_self`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.bc`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.bc_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.specMap_comp_eA`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.bc_comp_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.bc_comp_retr`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.NatC`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.SurjC`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.InjC`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.UnivC`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.ptM_congr`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.uM`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.vM`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.uM_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.vM_w`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.comp_vM`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.comp_eA`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.comp_uM`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.exists_lift`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.ptH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.ptH_comp_j`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.ptH_comp_j_of_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.one_of_factor`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.natH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.surjH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.injH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.unramH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm.piecesH`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq` (same contribution).
Other imports: none.
