# The core of Faltings' argument

This module formalizes the final dimension count in Faltings' proof of Stacks, More on Algebra,
Proposition 15.36.1 (07E5), (2) ⇒ (4) (the "big diagram"). The source works with `Ω_{−/𝔽_p}`;
Lean uses `Ω_{−/ℤ}`, which is the same module in characteristic `p`. The source identifies
`H₁(L_{K/A})` with `𝔪/𝔪²`. Here the rows are written with `H₁(L_{κ/A})` directly; the
identification is only used later (`FaltingsEmbdim`). All declarations live in
`Langlands.CommutativeAlgebra.Popescu.Faltings`.

Setting: `A → A'` is a local homomorphism of local rings, `κ = κ(A)`, `κ' = κ(A')`.

## The diagram

- First row (tensored with `κ'` over `κ`):
  `κ' ⊗ H₁(L_{κ/A}) → κ' ⊗ (κ ⊗_A Ω_{A/ℤ}) → κ' ⊗ Ω_{κ/ℤ}`, with maps `κ' ⊗ δ_A` and
  `κ' ⊗ (κ ⊗ Ω_A → Ω_κ)`.
- Second row: `H₁(L_{κ'/A'}) → κ' ⊗_{A'} Ω_{A'/ℤ} → Ω_{κ'/ℤ}`.
- Vertical maps:
  - `α`: the `κ'`-linear extension of `H₁(L_{κ/A}) → H₁(L_{κ'/A'})`;
  - `β = betaMap`: `κ' ⊗_κ (κ ⊗_A Ω_A) ≅ κ' ⊗_A Ω_A → κ' ⊗_{A'} Ω_{A'}`;
  - `γ = KaehlerDifferential.mapBaseChange ℤ κ κ'`.

## Declarations

- `betaMap`, `betaMap_tmul`: the map `β` and its value `c ⊗ (d ⊗ ω) ↦ (d c) ⊗ ω|_{A'}`.
- `square_left`: `β ∘ (κ' ⊗ δ_A) = δ_{A'} ∘ α`. The proof checks it on pure tensors using
  `δ_square`.
- `kaehler_map_square`: `Ω_{A/ℤ} → Ω_{κ/ℤ} → Ω_{κ'/ℤ}` equals `Ω_{A/ℤ} → Ω_{A'/ℤ} → Ω_{κ'/ℤ}`.
  Both are derivations-induced maps that agree on `da` (`Derivation.liftKaehlerDifferential_unique`).
- `square_right`: `γ ∘ (κ' ⊗ p_A) = p_{A'} ∘ β`, checked on pure tensors.
- `baseMap_eq_lTensor`: `baseMap` is `κ' ⊗_{A'} (A' ⊗_A Ω_A → Ω_{A'})` after cancelling base
  change.

The remaining declarations assume a presentation `Q : Generators A A' (Fin n)` with
`Q.ker = rootIdeal p b` (`hker`), that is, `A' = A[x]/(x_j^p − b_j)`.

- `ker_betaMap_le` (with `p = 0` in `A'`): `ker β` is contained in the `κ'`-span of the
  `1 ⊗ 1 ⊗ db_j`. Proof:
  1. `Ω_{A'/A}` is free (`exists_kaehler_basis`), hence projective.
  2. So `ker(κ' ⊗ φ)` is the image of `κ' ⊗ ker φ` (`ker_lTensor_eq_range`), where
     `φ : A' ⊗_A Ω_A → Ω_{A'}`.
  3. `ker φ = image δ` is contained in the `A'`-span of the `1 ⊗ db_j` (`range_δ_le_span`).
  4. Transport through the two `cancelBaseChange` isomorphisms.
- `rank_coker_betaMap_ge` (with `p = 0` in `A'`): `dim coker β ≥ n`. The map
  `κ' ⊗ Ω_{A'} → κ' ⊗ Ω_{A'/A}` kills the image of `β`, is surjective, and its target has dimension
  `n`, since `Ω_{A'/A}` is free of rank `n`.
- `charP_of_algebra`: characteristic `p` passes along ring maps into nontrivial rings.
- `rank_ker_gamma`: `dim ker γ = dim H₁(L_{κ'/κ})`, because `ker γ = image δ` and `δ` is injective
  in characteristic `p` (`δ_injective_of_charP`).
- `rank_coker_gamma`: `dim coker γ = dim Ω_{κ'/κ}`, by exactness at `Ω_{κ'/ℤ}`.
- `row_injective`, `row_surjective₀`, `row_exact`, `row_surjective`: exactness of the first row,
  `0 → κ' ⊗ H₁(L_{κ/A}) → κ' ⊗ (κ ⊗ Ω_A) → κ' ⊗ Ω_κ → 0`. The base change `κ' ⊗_κ −` is exact.
  The left map is injective by `δ_injective_of_charP` and flatness. The right map is surjective
  because `A → κ` is.
- `rank_baseChange_h1`: `dim_{κ'} κ' ⊗_κ H₁(L_{κ/A}) = dim_κ H₁(L_{κ/A})`.
- `snake_beta`: applies the snake count `rank_coker_le_rank_ker` to the diagram, giving
  `dim coker β ≤ dim ker β`. Its hypotheses are:
  - `dim H₁(L_{κ/A}) < ∞`;
  - `dim H₁(L_{κ'/A'}) ≤ dim H₁(L_{κ/A})`;
  - `dim H₁(L_{κ'/κ}) = dim Ω_{κ'/κ} < ∞` (Cartier).

  The second row is exact because `δ_{A'}` is injective in characteristic `p`.

## `faltings_core`

Assume, in addition to the presentation hypothesis, that `A` has characteristic `p` and the
`snake_beta` hypotheses hold. Then the `1 ⊗ db_j` are linearly independent over `κ` in
`κ ⊗_A Ω_{A/ℤ}`.

Proof:
1. Combining the bounds gives
   `n ≤ dim coker β ≤ dim ker β ≤ dim span(1 ⊗ 1 ⊗ db_j) ≤ n`.
2. So the `n` vectors `1 ⊗ 1 ⊗ db_j` span an `n`-dimensional space and are linearly independent over
   `κ'` (`linearIndependent_iff_card_eq_finrank_span`).
3. Restricting scalars to `κ` and composing with `κ ⊗ Ω_A → κ' ⊗_κ (κ ⊗ Ω_A)`, `v ↦ 1 ⊗ v`, gives
   independence over `κ` (`LinearIndependent.restrict_scalars`, `LinearIndependent.of_comp`).

This replaces the source's "kernel and cokernel of `β` have the same dimension": only the
inequality `dim coker β ≤ dim ker β` is needed, together with `dim coker β ≥ n`.
