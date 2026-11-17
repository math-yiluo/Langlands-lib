# Proof that the spectrum projection of a ground field extension is surjective

Authors: Worker 69 (proof and original documentation), Worker 233 (verification
and source clarification). Reused from Task 7100 shared draft revision 3.

`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.spectrumProjection_surjective`
proves `SpectrumProjectionSurjectiveStatement.{u, v}`. Let `K` (universe `u`)
and `L` (universe `v`) be complete ultrametric normed fields with
`NormedAlgebra K L`, and let `A` be a presented `K`-affinoid algebra. Then
every point `x` of the Berkovich spectrum of `A` equals
`spectrumProjection K L A y` for some point `y` of the spectrum of the ground
field extension `A_L = algebra K L A`.

The proof makes no assumption on the extension `L/K`, the valuations, or the
presentation of `A`. The argument works directly in the universe `max u v`,
so no transport between universes is needed.

## Helper lemma

`norm_map_eq_of_norm_map_le` states the following. Let `F` and `M` be normed
fields and let `f : F →+* M` satisfy `‖f a‖ ≤ ‖a‖` for all `a`. Then
`‖f a‖ = ‖a‖` for all `a`. Proof: `a ↦ ‖f a‖` is a multiplicative seminorm
bounded by the norm of `F`, so it is a point of `BanachSpectrum F`. By `BanachSpectrum.field_apply`, every point of the
spectrum of a normed field is its norm.

## Proof of the theorem

Fix `x`.

1. Let `H = CompletedResidueField K x` and let
   `χ = completedResidueMap K x : A → H`. This is a bounded `K`-algebra map
   with `‖χ a‖ = x a` (`norm_completedResidueMap`).
2. `exists_ultrametricTensorSeminorm` (with `E = K`, `F = H`, `G = L`) gives
   a ring seminorm `p` on `H ⊗[K] L`. It satisfies `p 1 = 1`, it is
   nonarchimedean, and it is bounded on the two legs by
   `p (a ⊗ 1) ≤ ‖a‖` and `p (1 ⊗ b) ≤ ‖b‖`.
3. `BanachSpectrum.nonarchimedeanDomination` gives a nonarchimedean
   multiplicative ring seminorm `q ≤ p` on `H ⊗[K] L`.
4. `seminormRealization` realizes `q`. It gives a complete ultrametric normed
   field `M` and a ring map `r : H ⊗[K] L → M` with `‖r t‖ = q t`. Both
   results are applied in the universe `max u v` of `H ⊗[K] L`.
5. Let `f₀ = r ∘ (a ↦ a ⊗ 1) : H → M` and `g₀ = r ∘ (b ↦ 1 ⊗ b) : L → M`. By
   steps 2–4, `‖f₀ a‖ ≤ ‖a‖` and `‖g₀ b‖ ≤ ‖b‖`. The helper lemma upgrades
   both to equalities. The two maps agree on `K`, because
   `includeLeftRingHom_comp_algebraMap` gives `a ⊗ 1 = 1 ⊗ a` for `a ∈ K`.
6. Make `M` a normed `L`-algebra through `g₀` and a normed `K`-algebra
   through `g₀ ∘ algebraMap K L`. Then `IsScalarTower K L M` holds by
   definition. The `norm_smul_le` bounds follow from `‖g₀ b‖ = ‖b‖` and
   `norm_algebraMap'`.
7. `φ = f₀ ∘ χ : A → M` is a bounded `K`-algebra map. It commutes with `K`
   by step 5, and it is bounded because `f₀` is isometric and `χ` is bounded.
8. The universal property of the ground field extension (`lift K L A M φ`)
   gives a bounded `L`-algebra map `ψ : A_L → M` with `ψ ∘ ι = φ`
   (`lift_iota`).
9. Take `y = BanachSpectrum.comap ψ (fieldPoint M)`, the norm of `M` pulled
   back along `ψ`. For `a ∈ A`, the goal unfolds definitionally (as in
   `spectrumProjection_apply`) to `‖ψ (ι a)‖ = x a`. This follows from `lift_iota`, from `f₀` being an
   isometry, and from `norm_completedResidueMap`. `BanachSpectrum.ext`
   concludes.

## Relation to the literature

Berkovich (*Spectral theory and analytic geometry over non-Archimedean
fields*, AMS 1990, proofs of Propositions 2.2.3(ii) and 2.2.4, printed
p. 29 / PDF p. 43) invokes the surjectivity of
`𝓜(𝒜 ⊗̂_k L) → 𝓜(𝒜)` and calls the projection the canonical surjective
map. The registered original is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The implemented proof derives this fact for the Library's presented ground
field extension using its universal property. It realizes `x` in `𝓗(x)` and
builds a common complete field directly from a multiplicative seminorm on
`𝓗(x) ⊗_K L` dominated by an ultrametric tensor seminorm. The imported tensor
seminorm, domination and realization proofs supply these ingredients; their
paired Markdown documents their provenance. The argument uses the two leg
bounds and normalization at one, and does not require multiplicativity of
the tensor seminorm itself. The single-universe amalgamation results
`pointAmalgamation` and `completeFieldAmalgamation` are not used.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
