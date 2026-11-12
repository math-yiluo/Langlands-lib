# Closedness of the weak Chow cover over the chart

For weak Chow data `D : ChowData X` (module `Construction`), this module proves that
the projection `q₂ : U ×_X W ⟶ W` is a proper morphism of schemes (`isProper_q₂`).
Here `φ : h_U → X` is the cover and `π : h_W → X` the chart. This is the closedness
step of Stacks Lemma 089I: the graph of `U ⇢ X` over the chart is closed in
`Z ×_S W`.

## Definitions

- `Q := U ×_X W`, the scheme `spacePullback φ π`, with projections `q₁ : Q ⟶ U` and
  `q₂ : Q ⟶ W`. `q₁` is étale because `π` is.
- `m : Q ⟶ Z ×_S W`, the pairing of `q₁` followed by the open immersion `U ⟶ Z` with
  `q₂`. Then `q₂ = m ≫ snd` (`q₂_eq`).
- `Γ i`: the set of points of `Z ×_S W` where the two morphisms
  `fst ≫ ζ ≫ p i` and `snd ≫ ι ≫ o` to `Y` agree, in the sense of `EqAt`. It is closed
  (`isClosed_Γ`, because `Y` is separated over `S`).

## Results

- `m` is a preimmersion: `m = (q₁, q₂) ≫ (U ↪ Z) × W`. The first factor is a closed
  immersion because `X` is separated (`isClosedImmersion_spacePullbackLift`); the
  second is an open immersion, a base change of `U ↪ Z` (`Over.whiskerRight_left`).
- `Γ_subset_range`: each `Γ i` lies in the range of `m`. For `x ∈ Γ i` take the
  residue-field point `h : Spec κ(x) ⟶ Z ×_S W`. By agreement at `x`, `h ≫ fst` lands
  in `opens i` and factors through `fac i` with composite `h ≫ snd`
  (`comp_fac_eq`). By `φ_spec` the resulting point of `U` and the point `h ≫ snd` of
  `W` have the same image in `X`, so they define a point of `Q` whose image under `m`
  is `h`. The closed point of `Spec κ(x)` maps to `x`.
- `dense_εU_image`: the image under `εU` of the complete part of `Gbar` is dense in
  `U`. Its image in `Z` contains the dense set `A` (`A_subset`, `dense_A`), and `U` is
  open in `Z`.
- `preimage_subset_Γ`: every point `y` of `Q` with `q₁(y) = εU(g)` and `gbar(g)`
  complete maps into `⋃ i, Γ i`. Proof: choose a point `z` of the scheme fibre product
  `R = Q ×_U Gbar` over `(y, g)` (`Scheme.Pullback.exists_preimage_pullback`). On `R`,
  the points `r₁ ≫ q₂` of `W` and `r₂ ≫ gbar` of the fibre power have the same image in
  `X` as the first coordinate (`εU_φ`). Completeness of `gbar(g)`
  (`exists_eqAt_of_mem_completeLocus`) gives `i` with `r₁ ≫ q₂` agreeing with
  `r₂ ≫ gbar ≫ pr i` at `z`. Composing with `ι ≫ o` and using
  `εbar ≫ ζ = gbar ≫ ε` and `ε ≫ p i = pr i ≫ ι ≫ o` shows that `r₁ ≫ m` lands in
  `Γ i` at `z`. `eqAt_comp_iff` then transports this to `m(y)`.
- `range_m`: the range of `m` is `⋃ i, Γ i`. The inclusion `⊆` holds because the
  preimage under `m` of the closed set `⋃ i, Γ i` contains the preimage under `q₁` of
  the dense set of `dense_εU_image`, which is dense since the étale `q₁` is open.
- Hence `m` is a closed immersion (`IsClosedImmersion.of_isPreimmersion`). The
  projection `Z ×_S W ⟶ W` is proper, being a base change of the proper `Z → S`.
  So `q₂ = m ≫ snd` is proper (`isProper_q₂`).
