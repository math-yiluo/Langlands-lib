# Sufficiency: vanishing obstruction cohomology gives lifts of isomorphisms

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Sufficiency`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

The notation is that of `OpennessOfVersality.CechData`, `OpennessOfVersality.Obstruction`,
`OpennessOfVersality.FrameCoord` and `OpennessOfVersality.Transitions`. We write
`T = testCover f K A`, `ι₀ = (P → A₀)` and `ι_A = (P → A)` as `R`-algebra maps.

## Main theorem

`exists_lift`. Hypotheses:
- `f : X ⟶ Spec R` is separated and flat. `K` is an ordered affine cover of
  `relSpace f P`. `π : P → A₀` is surjective (`hπ`).
- `jQ : Q →ₗ[P] P` has image `ker π` (`hjQ`). `D : Derivation R P F` is a derivation.
- `g` is a family of units on the pairwise intersections of `K` with
  `hg : defect g ∈ (ker π)`-extension (as in `Obstruction`).
- `L₀` is a line bundle on `relSpace f A₀` with frames `e i` on `(testCover f K A₀).U i`
  and transition functions `pushUnits (relMap ι₀) g`, i.e. the reductions of `g`.
- A test: an `R`- and `P`-algebra `A`, an `R`-algebra `B`, `χ : A₀ →ₐ[R] B`, and a
  surjection `q : A →ₐ[R] B` with nilpotent kernel. They satisfy
  `hqρ : q ∘ ι_A = χ ∘ ι₀`.
- An `A₀`-module `M` with `jM : M →ₗ[P] A` injective, with image `ker q` and
  square-zero products.
- `hH`: `ObstructionCone.HOneVanishes` holds for the complex `cplx f K A₀`, the
  differential `dif`, `δ = deltaMap`, `θ = thetaObs`, `z = zObs` and coefficients `M`.
- A line bundle `N` on `relSpace f A` and an isomorphism
  `φ : (relMap χ)^* L₀ ≅ (relMap q)^* N`.

Conclusion: there are `χ' : A₀ →ₐ[R] A` with `q ∘ χ' = χ` and an isomorphism
`ψ : (relMap χ')^* L₀ ≅ (𝟙)^* N`. They satisfy
`LineBundleFlatDescent.tr (relMap q) _ _ ψ.hom = φ.hom`, i.e. `ψ` restricts to `φ` on
`relSpace f B`.

Proof as implemented:
1. `exists_frames_lift`: frames `fr i` of `N` on `T.U i` whose pullbacks are the images
   under `φ` of the pulled-back frames `e i` (`HasCoord φ e fr … 1`). It uses
   `NilpotentFrame.exists_frame_lift`, the FLT `IsFrameOn.map_iso` and
   `testCover_preimage_le`.
2. `h' = frameCocycle fr` (transition functions of `N`).
   `pullbackCocycle_frameCocycle_eq`: their reductions to `relSpace f B` are the
   reductions of `g`, by uniqueness of transition functions (`IsTransition.unique`),
   `isTransition_pullback_push` and `isTransition_map`.
3. `pair_sub_mem`: `h' − (ι_A)_* g` lies in the extension of `ker q` on each pairwise
   intersection (`ker_appLE_eq_map`). `cvec σ = h'_σ · ((ι_A)_* g_σ)⁻¹ − 1`
   (`cvec_mem`), so `exists_cObs` gives `c ∈ C¹ ⊗ M` with `compMap jM c = cvec`.
4. `cObs_cocycle`: `d c + (phiQ)_* z = 0`, where `phiQ : Q →ₗ[A₀] M` satisfies
   `jM ∘ phiQ = ι_A ∘ jQ` (`phiQ`, `jM_phiQ`). Proof: on each triple intersection
   (`cObs_cocycle_apply`) it combines
   - `compMap_dif` and `d_one_apply` for `d c`;
   - CechData `compMap_natural` along `P → A`, with `compMap_zObs`, for `φ_* z`;
   - the cocycle identity of `h'` (`pr_cocycle`);
   - the ring identity `dc_core'` (proved by `linear_combination`);
   - the square-zero hypotheses (`ker_sq_zero`, `mul_eq_zero_of_mem_map_sq`).
   Then `compMap_injective` applies.
5. `hH` gives `b ∈ C⁰ ⊗ M` and `D' : F →ₗ[A₀] M` with `c = d b + D'_* θ` and
   `phiQ + D' ∘ δ = 0`.
6. `evMap : Thick P F →ₐ[P] A`, `(p, x) ↦ ι_A p + jM (D' x)`, and
   `rhoCorr = evMap ∘ ofDerivation D : P →ₐ[R] A`, i.e. `p ↦ ι_A p + jM (D' (D p))`
   (`rhoCorr_apply`). It kills `ker π`, so `descendAlg` gives `χ'` with
   `χ' ∘ ι₀ = rhoCorr` (`descendAlg_comp`, Mathlib `RingHom.liftOfSurjective`). Then
   `q ∘ χ' = χ`.
7. `compMap_thetaObs_ev`: the image of `D'_* θ` is `rhoCorr_* g · (ι_A)_* g⁻¹ − 1`.
   This is CechData `compMap_natural` along `evMap`, with `secMapAlong_comp_testMap`,
   `evMap_inr` and `preimage_rhoCorr`.
8. The gauge relation. With `b_i` the value of `compMap jM b` at the vertex `i` (`bvtx`),
   `gauge_sigma` proves on each edge
   `(1 − b_i) · rhoCorr_* g = h' · (1 − b_j)`. It uses `d_zero_apply`, the ring identity
   `gauge_core'` and the square-zero facts. `gauge_pair` restricts this to `T.U i ⊓ T.U j`,
   using the simplices `vtx`, `edge`, `le_inter_vtx`, `le_inter_edge`, `face_edge_zero`,
   `face_edge_one`, `res_pr_edge` and `res_cochain_congr`.
9. The restricted pullbacks of `e` along `relMap χ'` and the frames `(𝟙)^* fr` have
   transitions `rhoCorr_* g` and `h'` (`isTransition_pullback_push`,
   `LineHom.isTransition_pullback`, `id_appLE_apply`). `1 − b_i` is a gauge family of
   units (`LineHom.isGaugeFamily_iff_of_lt`). `exists_iso_of_gauge` gives `ψ`.
10. `tr_eq_of_hasCoord`: on `relSpace f B` both `tr ψ` and `φ` have coordinate `1`. The
    reduction of `1 − b_i` is `1` because `b_i` lies in the `ker q`-extension
    (`ker_appLE_eq_map`).

## Auxiliary declarations

`testCover_preimage_le`, `testCover_pair_le` (preimage inclusions from `hqρ`),
`isAffineOpen_testCover_inf` (pairwise intersections of the test cover are affine, by
Mathlib's `isAffineHom_diagonal_iff`), `exists_jM_eq`, `secMapAlong_comp_testMap`.

## Provenance

Internal construction for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It formalizes,
in Čech terms, the standard argument that lifting a line bundle together with its base
point along a square-zero extension is unobstructed when the first cohomology of the
obstruction cone vanishes. No literature statement is formalized.
