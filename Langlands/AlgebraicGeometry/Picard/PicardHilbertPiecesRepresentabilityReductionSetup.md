# Abel classes of the divisor scheme and the classification of linear systems

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is part of the proof
of `PicardHilbertPiecesRepresentabilityReductionStatement`; the main theorem
and the full route are in `PicardHilbertPiecesRepresentabilityReductionProof.md`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. The module sets up the data of Kleiman's construction
(*The Picard scheme*, proof of Theorem 4.8, pp.29–31): the class of a point of
the divisor scheme, and the classification of the divisors of a linear system
by points of the divisor scheme.

## General lemmas

- `mapX_congr`: `mapX` depends only on the morphism, not on the proof of
  commutativity.
- `relativeSpace_map_sym`: `(relativeSpace f).map k` corresponds to
  `mapX f k.left` under the symmetries `sym`.
- `bcIso f h w : X ×_S T' ≅ (X ×_S T) ×_T T'` for `h : T' ⟶ T` over `S`, with
  its projections `bcIso_hom_fst`, `bcIso_hom_snd`, `bcIso_inv_snd`,
  `bcIso_inv_mapX`. This identifies the family over `T'` in the
  linear-system statement (b) with the family `X ×_S T'` of the other
  statements.
- `bcIso_hom_map`: under `bcIso`, the comparison maps
  `pullback.map … k …` of (b) become `mapX f k`.
- `comap_injective_of_iso`: comap of ideal sheaves along an isomorphism is
  injective.
- `comap_preimage_ι_self`, `eq_top_of_preimage_eq_top` (for a surjective map),
  `range_subset_of_preimage_eq_top`: facts about opens and preimages.
- `mem_fppf_over`: a sieve on `T` in `Over S` that contains one flat,
  surjective, locally finitely presented arrow is an fppf covering sieve. The
  proof uses `GrothendieckTopology.mem_over_iff` and
  `Hom.singleton_mem_fppfPrecoverage`.

## The data of the construction

Fix `f : X ⟶ S`, an invertible `𝓛X` on `X`, `d : D ⟶ S`, a relative
effective divisor `W` on `X ×_S D` and `m : ℕ`.

- `cP s`: the class of `𝓛X` pulled back to `X ×_S T`. `pb_mapX_cP` gives its
  base change.
- `cLW = dcl W - m • cP d`, the class of `O(W) ⊗ O(-m)`. `LW` is an
  invertible module with this class (`Group.lineBundleRepresentative`), so no
  dual of `𝓛X` is needed. `isInvertible_LW` and `icl_LW` record its
  properties.
- `pt y w`: the class `(mapX y)^* cLW` on `X ×_S T` for a point `y : T ⟶ D`.
  `pt_congr` and `pb_mapX_pt` give its naturality.
- `icl_twist_pt`: the class of `((mapX y)^* L_W)(m)` is `pt y + m • cP`.
- `dcl_comap_mapX`: the divisor `y^* W` has class `pt y + m • cP`. This uses
  the base-change hypothesis through `divBC`. So `O(y^* W)` and
  `((mapX y)^* L_W)(m)` have the same class.
- `Classifies f d W`: the universal property of the divisor scheme in
  `RelativeEffectiveDivisorHilbertPiecesStatement`, as a proposition.
  `classifies_rel` (the comap along a point is relative effective Cartier)
  and `classifies_eq` (points with the same comap are equal) are its two
  uses.
- `linsys_classify`: let `W_Λ` be a relative effective divisor on
  `(X ×_S T) ×_T Λ` over `l : Λ ⟶ T`, with
  `O(W_Λ) ≅ pr^* M ⊗ pr^* N_Λ`. Then there is a point `y : Λ ⟶ D` with
  `y^* W = W_Λ` (after `bcIso`) and
  `pt y + m • cP = l^*[M] + pr^*[N_Λ]`. The proof first moves `W_Λ` to
  `X ×_S Λ` with `flat_comap` along the isomorphism `bcIso`. Then
  `Classifies` gives `y`, and `dcl_comap_mapX` gives the class.

## The opens

- `HU1`, `HU2`: the first two hypotheses on the opens `U` in
  `PicardHilbertPiecesRepresentabilityStatement` (invariance under twists from
  the base, and base change), copied as propositions.
- `U_eq_preimage`: let `L` on `X ×_S T` satisfy `icl L = pt y + pr^* n` for a
  point `y` of `D` and some `n ∈ Pic(T)`, where `T` and `D` are locally
  noetherian. Then `U T s L c m = y⁻¹ U D d L_W c m`. Indeed `hU1` replaces `L`
  by `(mapX y)^* L_W`, and `hU2` computes its open.

## Abel classes

- `ab T y w`: the class `sym^* (pt y)` on `T ×_S X` for `y : T.left ⟶ D`.
- `pb_ab`: `ab` is natural in `T`.
