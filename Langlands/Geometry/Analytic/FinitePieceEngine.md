# Test maps out of the finite pieces of an affine analytification map

Lean module: `Langlands.Geometry.Analytic.FinitePieceEngine`
(namespace `Langlands.Analytic.AffineAnalytification.FinitePieceLocal`). Support module for
the proof of `AffineAnalytificationFiniteGermComparisonStatement`.

## Content

* `exists_restriction_idempotent`: let `Q ⊆ P` be recognized subsets of a saturated atlas whose
  chart preimage `P.chart⁻¹(Q.locus)` is clopen. Then there is an idempotent `e` of `P.algebra`
  with `Q.restriction P h e = 1` such that `Q.restriction P h x = 0` implies `e * x = 0`.
* `exists_test_factorization`: the setting is a piece of `g := saturatedHom K P Q f` with
  `V` open, a recognized `W` with algebra `R`, and a recognized `V'` with
  `V'.locus = V ∩ g⁻¹(W.locus)`, algebra `S` and bounded map `φ : R → S`. Let `E` be a complete
  ultrametric normed `K`-algebra (in any universe), `τR : R → E` a bounded map, and
  `τB : B →ₐ[K] E` with `τB ∘ f = τR ∘ recMap`. Then there are a presented affinoid algebra `D`,
  a bounded map `r : R → D`, a map `bm : B → D` compatible with `f` and `recMap`, bounded maps
  `ρ : D → S` and `θ : D → E`, and an element `e : D`, such that:
  * `ρ ∘ r = φ`, `ρ ∘ bm = recMap Q V'`, `θ ∘ r = τR` and `θ ∘ bm = τB`;
  * `ρ` is surjective, `e` is idempotent, `ρ e = 1`, and `ρ x = 0` implies `e x = 0`;
  * two bounded maps out of `D` (into a normed `K`-algebra in universe `u`) that agree on the
    images of `r` and `bm` are equal.

## Proofs

* `exists_restriction_idempotent`: the clopen chart preimage gives a clopen rational domain
  `d := clopenRationalChart` of `P.algebra`, with idempotent `clopenIdempotent`. Both `d` and the
  restriction to `Q` represent the same subset. The universal properties give mutually inverse
  factorizations, so the restriction to `Q` is `ψ₁ ∘ d.baseMap` with `ψ₁` injective. The
  properties of `e` then follow from `baseMap_clopenIdempotent` and
  `clopenIdempotent_mul_eq_zero`.
* `exists_test_factorization`:
  1. Choose the level `m` of an original chart `i` of `B` that contains `V'.locus` and admits
     `τB`. `τB` extends to a bounded `τi` on the chart algebra (`exists_orig_lift`). Choose an
     original chart `j` of `A` containing `W.locus` and the image of the chart `i`
     (`exists_orig_superset`, compactness).
  2. `D` is the affinoid pushout (`AffinoidPushout`) of the chart map
     `φij := g.pullback i j` and the restriction `W.containedRestriction j`. `r` and `bm` are its
     right leg and its left leg composed with `satMap Q i`. `θ` is
     `AffinoidPushout.lift τi τR`. The compatibility `τi ∘ φij = τR ∘ restriction` holds by
     `orig_hom_ext` on `A`, using `hτ`.
  3. `V''`, the published `StrongHom.recognizedPullback`, is the recognized preimage of `W` in the
     chart `i`, with locus `chart_i ∩ g⁻¹(W.locus)`.
     `fullRecognitionPullbackEquiv` identifies its algebra with `D`. `ρ` is this equivalence
     followed by `V'.restriction V''`. The leg identities use
     `fullRecognitionPairs_pullback_eq_pushout`, `restriction_comm` and
     `boundedEquivOfLocusEq_comp_baseMap`.
  4. Since `V'.locus = V''.locus ∩ V` with `V` open, `isClopen_chart_preimage_of_eq_inter` makes
     `V'` clopen in `V''`. `restriction_flat_and_surjective` gives surjectivity of `ρ`, and
     `exists_restriction_idempotent` gives `e`, transported through the equivalence.
  5. Uniqueness: `AffinoidPushout.hom_ext`, with `orig_hom_ext` on the left leg.

## Provenance

Internal. This is the analytic step of the derived argument for condition 4 of
`AffineAnalytificationFinitePieceLocalStatement` ("Why condition 4 holds", step 1, in that
statement's Markdown). It realizes the piece `V'` as a direct factor of the affinoid pushout of
a chart algebra and `R`. Everything it uses about recognized subsets, affinoid pushouts and clopen
domains is published Library material.
