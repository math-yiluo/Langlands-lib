# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.CoprodPtsA (lift)` is dropped; see the port edit below. The command `export _root_.CoprodPtsA (iSup_opensRange)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 43, line 63 here): `rw [← Scheme.Hom.preimage_iSup, iSup_opensRange, Scheme.Hom.preimage_top]` is replaced by `rw [← Scheme.Hom.preimage_iSup, _root_.CoprodPtsA.iSup_opensRange, Scheme.Hom.preimage_top]`. FLT `p2m_export "CoprodPtsA" "iSup_opensRange"` aliases the private declaration(s) `_root_.CoprodPtsA.`, `_root_.iSup_opensRange.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `CoprodPtsA` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- Universe generalization: The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. The FLT lemma is stated for coproducts indexed by `σ : Type u` of schemes in universe `u`. The Hilbert scheme is a coproduct over `Polynomial ℚ : Type` of schemes in universe `uz`, so the index type is generalized to `σ : Type*` with `[Small.{u} σ]` (such coproducts exist in `Scheme.{u}`). This generalizes the statement: for `σ : Type u` the instance `Small.{u} σ` holds, giving the FLT statement. The FLT proof used `sigmaMk : (Σ i, X i) ≃ₜ ∐ X`, which Mathlib only provides for `σ : Type u`; it is replaced by an argument with the open cover `sigmaOpenCover` (the ranges of the `Sigma.ι` cover `∐ X`) and the pairwise disjointness of these ranges (`disjoint_opensRange_sigmaι`). The changed lines are:
  - line 25 here:
    FLT text (universe-0 port):

    ```lean
    variable {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H)
    
    theorem range_sigmaι_eq (i : σ) :
        Set.range (Sigma.ι H i).base = sigmaMk H '' Set.range (Sigma.mk i) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨⟨i, x⟩, ⟨x, rfl⟩, sigmaMk_mk H i x⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, (sigmaMk_mk H i x).symm⟩
    ```

    replacement:

    ```lean
    variable {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H)
    ```
  - lines 28–48 here:
    FLT text (universe-0 port):

    ```lean
      rw [Scheme.Hom.coe_opensRange, range_sigmaι_eq]
      exact (sigmaMk H).isClosed_image.mpr isClosed_range_sigmaMk
    ```

    replacement:

    ```lean
      classical
      have hcov : (⨆ j, (Sigma.ι H j).opensRange) = ⊤ := by
        have h := (sigmaOpenCover H).iSup_opensRange
        simp only [sigmaOpenCover_f] at h
        exact h
      have hcompl : ((Sigma.ι H i).opensRange : Set ↥(∐ H))ᶜ =
          ⋃ j ∈ ({i}ᶜ : Set σ), ((Sigma.ι H j).opensRange : Set ↥(∐ H)) := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_compl_singleton_iff, exists_prop]
        constructor
        · intro hx
          have hx' : x ∈ ((⨆ j, (Sigma.ι H j).opensRange : (∐ H).Opens) : Set ↥(∐ H)) := by
            rw [hcov]; trivial
          rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx'
          obtain ⟨j, hj⟩ := hx'
          exact ⟨j, fun h => hx (h ▸ hj), hj⟩
        · rintro ⟨j, hji, hj⟩ hx
          exact Set.disjoint_iff.mp (Opens.coe_disjoint.mpr
            (disjoint_opensRange_sigmaι H i j (Ne.symm hji))) ⟨hx, hj⟩
      rw [← isOpen_compl_iff, hcompl]
      exact isOpen_biUnion fun j _ => (Sigma.ι H j).opensRange.isOpen
    ```
  - line 97 here:
    FLT text (universe-0 port):

    ```lean
        {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    ```

    replacement:

    ```lean
        {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`. Statement. `AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`: for a family of
schemes `(Hᵢ)` indexed by a `u`-small type `σ` (any universe) and `u : T ⟶ ∐ Hᵢ`, the preimages
`Tᵢ = u⁻¹(image of Hᵢ)` are closed (and open), pairwise disjoint and cover `T`; on each `Tᵢ` the map `u`
factors uniquely through `Hᵢ`; and if `T` is quasi-compact only finitely many `Tᵢ` are nonempty.

Proof (namespace `CoprodPtsA`). The images of the coproduct inclusions are open, pairwise disjoint
(Mathlib's `disjoint_opensRange_sigmaι`) and cover `∐ Hᵢ` (`sigmaOpenCover`), so each image is closed, its
complement being the union of the others (`isClosed_opensRange`). Preimages under `u` keep these
properties (`closed`, `disjoint`, `cover`). On `Tᵢ` the image of `u` lies in the image of the open immersion
`Sigma.ι H i`, giving the unique factorization (`range_subset`, `IsOpenImmersion.lift`). Finiteness follows
from compactness of `T` and disjointness (`finite`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.isClosed_opensRange`
- private theorem `CoprodPtsA.iSup_opensRange`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.closed`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.disjoint`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.cover`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.range_subset`
- private theorem `CoprodPtsA.lift`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.CoprodPtsA.finite`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
