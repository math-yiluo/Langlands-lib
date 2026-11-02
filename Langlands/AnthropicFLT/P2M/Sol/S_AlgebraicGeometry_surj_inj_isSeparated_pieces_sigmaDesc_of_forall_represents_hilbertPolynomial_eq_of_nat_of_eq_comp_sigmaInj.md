# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 18 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 26 here); in 81 lines the replacements `Type` (universe 0) → `Type uz` (49 places), `Scheme.{0}` → `Scheme.{uz}` (39 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization and pieces strengthening): Statement change (strengthening the Hilbert-polynomial pieces clause): the FLT clause `∀ Pℚ, ∃ U : Opens, IsClosed U ∧ QuasiCompact (U.ι ≫ π) ∧ (∀ families, range ⊆ U ↔ Hilbert polynomial Pℚ)` is replaced by `∃ U : Polynomial ℚ → Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧ ∀ Pℚ, IsClosed (U Pℚ) ∧ QuasiCompact ((U Pℚ).ι ≫ π) ∧ (…)`: the pieces form one family of pairwise disjoint opens covering the scheme. This is needed by the task (the relative endomorphism scheme is the disjoint union of its pieces) and implies the FLT clause. The pieces are the ones of the FLT proof (images of the coproduct inclusions, and their preimages in the later stages). In this file the pieces are the images `(Sigma.ι C Pℚ).opensRange` of the coproduct inclusions: the local lemma `pieces` now states its properties directly for this open (FLT: it existentially quantified over `U` and chose this open), and the main proof supplies the family, its pairwise disjointness (`disjoint_opensRange_sigmaι`) and the covering property (from the ported `Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma` applied to `𝟙 (∐ C)`). The other lines of these hunks change only by the universe generalization. The changed lines are:
  - lines 374–377 here:
    FLT text (universe-0 port):

    ```lean
        ∃ U : (∐ F.C).Opens, IsClosed (U : Set ↥(∐ F.C)) ∧ QuasiCompact (U.ι ≫ (Sigma.desc F.πC)) ∧
          ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```

    replacement:

    ```lean
        IsClosed ((Sigma.ι F.C Pℚ).opensRange : Set ↥(∐ F.C)) ∧
          QuasiCompact ((Sigma.ι F.C Pℚ).opensRange.ι ≫ (Sigma.desc F.πC)) ∧
          ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```
  - lines 379–380 here:
    FLT text (universe-0 port):

    ```lean
            (Set.range (F.pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set ↥(∐ F.C)) ↔
              ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
            (Set.range (F.pt S' s Z ι hι hfl hfp).1.base ⊆ ((Sigma.ι F.C Pℚ).opensRange : Set ↥(∐ F.C)) ↔
              ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
  - line 385 here:
    FLT text (universe-0 port):

    ```lean
      refine ⟨(Sigma.ι F.C Pℚ).opensRange, ?_, ?_, ?_⟩
    ```

    replacement:

    ```lean
      refine ⟨?_, ?_, ?_⟩
    ```
  - lines 840–843 here:
    FLT text (universe-0 port):

    ```lean
          (∀ Pℚ : Polynomial ℚ, ∃ U : (∐ C).Opens, IsClosed (U : Set ↥(∐ C)) ∧ QuasiCompact (U.ι ≫ (Sigma.desc πC)) ∧
            ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```

    replacement:

    ```lean
          (∃ U : Polynomial ℚ → (∐ C).Opens, Pairwise (Function.onFun Disjoint U) ∧ (⨆ Pℚ, U Pℚ) = ⊤ ∧
            ∀ Pℚ : Polynomial ℚ, IsClosed (U Pℚ : Set ↥(∐ C)) ∧ QuasiCompact ((U Pℚ).ι ≫ (Sigma.desc πC)) ∧
            ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
              (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    ```
  - lines 845–846 here:
    FLT text (universe-0 port):

    ```lean
              (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set ↥(∐ C)) ↔
                ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```

    replacement:

    ```lean
              (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U Pℚ : Set ↥(∐ C)) ↔
                ∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ```
  - lines 854–856 here:
    FLT text (universe-0 port):

    ```lean
        fun Pℚ => F.pieces hX₁ hX₂ Pℚ⟩
    ```

    replacement:

    ```lean
        ⟨fun Pℚ => (Sigma.ι C Pℚ).opensRange, fun P Q h => disjoint_opensRange_sigmaι C P Q h,
          (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma C
            (𝟙 (∐ C))).2.2.1, fun Pℚ => F.pieces hX₁ hX₂ Pℚ⟩⟩
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj`. Statement. `AlgebraicGeometry.surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj`:
in the setting of `exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`, assume each
`C P` represents (surjectively, and injectively up to isomorphism) the families with Hilbert polynomial `P`, is
proper and locally of finite presentation, and that `pt` into `∐ C` is natural and restricts to `ptC P ≫ ι_P` on
families with Hilbert polynomial `P`. Then `pt` is surjective and injective up to isomorphism, `∐ C ⟶ Spec S` is
separated and locally of finite presentation, and there is a family `U P` of pairwise disjoint opens covering
`∐ C`, each closed and quasi-compact over `Spec S`, such that a family lands in `U P` iff its Hilbert polynomial is
`P`.

Proof. Sections `Pow`, `BC`: twisted line bundles and base change of families (`bcObj`, `bc_flat`, `bc_lfp`,
`bc_HP`, `HP_of_isPullback`). Separatedness and finite presentation of `Sigma.desc πC` follow from the ported
`isSeparated_sigmaDesc_of_forall_isSeparated` and `IsZariskiLocalAtTarget_sigmaMap`. Section `Loc`/`pieces`: the
pieces are the images `U P` of `Sigma.ι C P` (see the changes above): they are clopen, pairwise disjoint and cover
(ported `Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`, local disjointness lemma), quasi-
compact over `Spec S` as `C P` is proper, and a family lands in `U P` iff its Hilbert polynomial is `P`
(`HP_iff`, using `exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`
and `Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback`). Section `Partition` (`T`, `isoT`, `jP`, `eP`): a point
`x : Spec S' ⟶ ∐ C` decomposes `Spec S'` into the clopen pieces `x⁻¹(U P)`, finitely many of which are nonempty,
each `Spec` of `S'` localized at an idempotent. Section `Surj`: on each piece `x` factors through `C P`, the
surjectivity of `ptC P` gives a family, and the families are glued over the disjoint union (`nonempty_isColimit_jP`,
`nonempty_isColimit_eP`, `isPullback_sigmaι_of_desc`); naturality identifies its point with `x`. Section `Inj`: two
families with the same point have the same pieces; on each piece they have the same `ptC P`-point, so they are
isomorphic, and the isomorphisms glue.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Lpow`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.hval`
- def `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.HP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.HP_iff`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.poly_eq_of_eventually`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.jmap`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.jmap_fst`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.jmap_snd`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.isPullback_jmap`
- scoped instance `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.isOpenImmersion_jmap`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.range_eq_of_isPullback`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.opensRange_jmap`
- def `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.powIsoOfComm`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.hval_eq_of_isPullback`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.HP_of_isPullback`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bcObj`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bcι`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bcE`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bc_comm`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.isPullback_bc`
- scoped instance `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bcι_isClosedImmersion`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bc_flat`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bc_lfp`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bc_HP`
- scoped instance `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.bcE_isOpenImmersion`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.opensRange_bcE`
- structure `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.eq_of_mem_opensRange`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.eventually_eq_of_range_subset`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.pieces`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.T`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.T_def`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isClosed_T`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.disjoint_T`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.iSup_T`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.eq_of_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.exists_idem`
- def `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.idem`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.coe_T_eq`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.A`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.ψ`
- scoped instance `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isOpenImmersion_ψ`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.range_ψ`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.opensRange_ψ`
- def `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isoT`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isoT_hom_ι`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isoT_inv_ψ`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.sP`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.jP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.opensRange_jP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.nonempty_isColimit_jP`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.ZP`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.ιP`
- abbrev `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.eP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.opensRange_eP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.nonempty_isColimit_eP`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.isPullback_sigmaι_of_desc`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.surj`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.HP_piece`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam.inj`
- theorem `P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated` (same contribution).
Other imports: none.
