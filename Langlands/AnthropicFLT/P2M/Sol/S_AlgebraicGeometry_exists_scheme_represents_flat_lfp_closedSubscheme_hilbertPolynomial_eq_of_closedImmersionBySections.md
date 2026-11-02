# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 33 here); in 64 lines the replacements `Type` (universe 0) → `Type uz` (48 places), `Scheme.{0}` → `Scheme.{uz}` (20 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT construction works over the absolute base `Spec ℤ`. With schemes in universe `uz`, the ring `ℤ : Type` can only serve as a base in universe 0, so the absolute base ring `ℤ` is replaced by `ULift.{uz} ℤ` (the ring `ℤ` lifted to universe `uz`, isomorphic to `ℤ`). The new helper module `Langlands.AlgebraicGeometry.ULiftIntAlgebra` provides the `ULift ℤ`-algebra structure of every commutative ring (`Langlands.ULiftInt.algebra`), algebra maps from ring maps (`Langlands.ULiftInt.toAlgHom`), uniqueness of ring maps out of `ULift ℤ` (`Langlands.ULiftInt.ringHom_ext`) and noetherianity of `ULift ℤ`. In this file `Langlands.ULiftInt.algebra` is declared as a local instance; `Langlands.ULiftInt.ringHom_ext` replaces `RingHom.ext_int`. In this file this concerns section `HS`, the base change of the Hilbert scheme of `ℙⁿ` from `Spec (ULift ℤ)` to `Spec S` (the local instance is declared for the section, and the `variable` lines are moved below it). The statement of the solution theorem only changes by the universe generalization. The changed lines are:
  - line 179 here:
    FLT text (universe-0 port):

    ```lean
    variable {n : ℕ} {h : ℕ → ℕ} (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of ℤ))
      (ptH : ∀ (A : Type) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ H))
      (hoverH : ∀ (A : Type) [CommRing A] (x : Point A n h), ptH A x ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
      (S : Type) [CommRing S]
    ```

    replacement:

    ```lean
    attribute [local instance] Langlands.ULiftInt.algebra
    ```
  - lines 181–186 here:
    FLT text (universe-0 port):

    ```lean
    abbrev HS : Scheme.{0} := pullback pH (Spec.map (CommRingCat.ofHom (algebraMap ℤ S)))
    ```

    replacement:

    ```lean
    variable {n : ℕ} {h : ℕ → ℕ} (H : Scheme.{uz}) (pH : H ⟶ Spec (CommRingCat.of (ULift.{uz} ℤ)))
      (ptH : ∀ (A : Type uz) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ H))
      (hoverH : ∀ (A : Type uz) [CommRing A] (x : Point A n h), ptH A x ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) A)))
      (S : Type uz) [CommRing S]
    
    abbrev HS : Scheme.{uz} := pullback pH (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) S)))
    ```
  - lines 190–193 here:
    FLT text (universe-0 port):

    ```lean
    theorem int_comp {A : Type} [CommRing A] (ψ : S →+* A) :
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
          Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (ψ.comp (algebraMap ℤ S)) (algebraMap ℤ A)]
    ```

    replacement:

    ```lean
    theorem int_comp {A : Type uz} [CommRing A] (ψ : S →+* A) :
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) S)) =
          Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) A)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Langlands.ULiftInt.ringHom_ext (ψ.comp (algebraMap (ULift.{uz} ℤ) S)) (algebraMap (ULift.{uz} ℤ) A)]
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`. Statement. `AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`
(the Hilbert scheme with fixed Hilbert polynomial): in the same setting and for a fixed `P : ℚ[X]`, there are a
proper, finitely presented `C ⟶ Spec S` and a natural assignment of `S`-points of `C` to the flat, finitely
presented closed subschemes of `X ×_S Spec S'` with Hilbert polynomial `P`, surjective, and injective up to
isomorphism of subschemes.

Proof. Section `Emb`: a presentation `𝔓` of `𝓛X` embeds `X` (and its base changes `X ×_S Spec S'`, `emb`) as a closed
subscheme of `ℙⁿ`, cut out on the standard charts by a finitely generated homogeneous ideal `I₀` (ported
`ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion`). If no graded ideal over a field
has Hilbert polynomial `P`, the empty scheme works. Otherwise choose `m` beyond the uniform bounds of the ported
`HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`,
`HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf` (the Hilbert scheme `H`
of `ℙⁿ` over `ULift ℤ` for the Hilbert function `hilbertFunctionOf n P m`),
`HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf` (its
universal family) and `HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`.
Section `HS`: `H` is base-changed to `S`. `C` is the closed subscheme of points whose ideal contains `I₀` in
degrees `≥ m` (ported
`HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg`),
i.e. whose subscheme lies in `X`. Section `Poly` and the main proof: the Hilbert polynomial of a family is computed
on geometric fibres (ported `exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom`),
so families with Hilbert polynomial `P` correspond to points of `C`; naturality, surjectivity and injectivity come
from the corresponding properties of `H`, using the ported `ProjSpace.isPullback_map`,
`ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map` and the ideal comparisons
`ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion`, `ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span`,
`ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span` (section `MapComp` for the compatibility of the maps
`ℙⁿ_A ⟶ ℙⁿ_B`). `C` is proper and finitely presented since `H` is and `C ⟶ H_S` is a finitely presented closed
immersion.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.PPn`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.comm_emb`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.emb`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.emb_π`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.emb_map`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.isPullback_emb`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.isClosedImmersion_emb`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.ker_emb_ideal`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.app_emb_eq_zero`
- abbrev `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.HS`
- abbrev `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.πHS`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.int_comp`
- def `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.ptHS`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.ptHS_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.ptHS_symm_apply`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.hnatHS`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.cast_hilbertFunctionOf`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.poly_eq_of_eval_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.HilbR_ringHom_eq_of_specMap_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.exists_isUnit_of_span_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.projMap_congr`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.mvMapGraded_comp`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.map_comp_map`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.preimage_spec`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg` (same contribution).
Other imports: none.
