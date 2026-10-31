# Left compact averaging of Whittaker model functions

Module `Langlands.Representation.GodementJacquet.WhittakerAveraging`.

This module proves the inclusion `I₃ ⊆ I₂` for the actual coefficient model,
with no hypothesis beyond smoothness of `σ`. It is one of the two inclusions
needed for `Langlands.GodementJacquet.WhittakerModelComparisonStatement`.

## Source and provenance

The idea is the left compact averaging of Jacquet, Piatetski-Shapiro and
Shalika, *Automorphic forms on GL(3)*, Ann. of Math. 109 (1979), equations
(3.1.3)–(3.1.4). Averaging a Whittaker function on the left over a compact open
subgroup that fixes the test function gives a matrix coefficient with the same
full-matrix integral. Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), Section (5.2), uses this to compare the
Laurent modules `I₂` and `I₃`.

The source states the averaging for irreducible generic representations. The
Lean statements here are internal and derived. They use only smoothness of `σ`:
no irreducibility, admissibility, Whittaker type or nonvanishing of `ℓ`. So
this proof covers the reducible scope of the target by itself. The averaging
measure is the restriction of the normalized Haar measure
`generalLinearHaar F.Carrier n` to a compact open subgroup `K`, and the average
is divided by its mass `μ(K)`. This is not a probability Haar measure on `K`.

## Declarations

### `Langlands.GodementJacquet.setIntegral_mul_right_of_mem`

Let `G` be a group with measurable multiplication and let `μ` be a
right-invariant measure. For a subgroup `K` with measurable carrier, any
`k ∈ K` and any `f : G → ℂ`:

`∫_{x ∈ K} f (x * k) dμ = ∫_{x ∈ K} f x dμ`.

Proof: right multiplication by `k` preserves `μ` and maps `K` onto itself, so
`MeasurePreserving.restrict_preimage` and `integral_comp` along the measurable
embedding `x ↦ x * k` give the equality.

### `Langlands.GodementJacquet.Padic.exists_nhds_matrixTest_invariant`

For every full-matrix Schwartz–Bruhat function `Φ` on `M_{n+1}(F)` there is a
neighbourhood `U` of `1` in `GL_{n+1}(F)` with `Φ (g M) = Φ M` for all `g ∈ U`
and all matrices `M`, singular ones included.

Proof: the map `(g, M) ↦ Φ (g M) - Φ M` is locally constant, so its zero fiber
is open. That fiber contains `{1} × tsupport Φ`, where `tsupport Φ` is compact.
The generalized tube lemma gives an open `u ∋ 1` with `Φ (h N) = Φ N` for
`h ∈ u` and `N ∈ tsupport Φ`. Take `U = u ∩ u⁻¹`. If `M ∈ tsupport Φ`, the
claim is immediate. If `g M ∈ tsupport Φ`, apply the claim to `g⁻¹ ∈ u` and
the matrix `g M`. If neither lies in the support, both values are `0`.

### `Langlands.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant`

There is a compact open subgroup `K` of `GL_{n+1}(F)` such that every `k ∈ K`
satisfies `Φ (k M) = Φ M` for all `M` and `|det k| = 1` for the normalized
absolute value.

Proof: intersect the neighbourhood above with the open kernel of the
determinant norm (`isOpen_ker_determinantNorm`). Then choose a compact open
subgroup inside that intersection (`generalLinearCompactOpen`).

### `Langlands.GodementJacquet.Padic.modelSetIntegral` and `modelSetIntegralDual`

For smooth `σ`, a functional `ℓ` and a compact open subgroup `K`, the map

`Λ_K (W') = ∫_{k ∈ K} W'(k) dμ(k)`

is a linear functional on the coefficient model
`(glCoefficientModel ψ n σ ℓ).toSubmodule`. The model functions are continuous
(`glModelFunction_continuous`, which uses smoothness of `σ`), so they are
integrable on the compact set `K`, and additivity follows from `integral_add`.

`modelSetIntegralDual` bundles `Λ_K` as an element of the smooth dual of
`glModelRepresentation ψ n σ ℓ`. It is fixed by `K`: for `k ∈ K`,
`(k · Λ_K)(W') = Λ_K (ρ(k⁻¹) W') = ∫_{x ∈ K} W'(x k⁻¹) dμ(x)`, and this equals
`Λ_K (W')` by `setIntegral_mul_right_of_mem`. That lemma uses right invariance
of `generalLinearHaar`, which comes from the unimodularity instance in
`Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity`.

### `Langlands.GodementJacquet.Padic.whittakerRationalValues_subset`

For smooth `σ` and any `ℓ : glFunctionals ψ n σ`:

`Padic.whittakerRationalValues F ψ σ ℓ ⊆ Padic.matrixRationalValues F (glModelRepresentation ψ n σ ℓ)`.

Here the right side is taken on the carrier
`(glCoefficientModel ψ n σ ℓ).toSubmodule`.

Proof: let `R` be a value of the Whittaker integral of `Φ` and a model element
`w`, with function `W = glModelFunction ψ n σ ℓ w`. Choose `K` for `Φ` as
above, and set `c = μ(K)⁻¹`, which is finite and nonzero since `K` is compact
and open. The vector `w` is smooth in the model (`glModel_isSmooth`). Its
bi-smooth coefficient against `Λ_K` is

`g ↦ Λ_K (ρ(g) w) = ∫_{x ∈ K} W (x g) dμ(x)`,

because `ρ(g)` is right translation (definitional). Let `f` be `c` times this
coefficient, an element of `biSmoothMatrixCoefficients`. For every `s` at which
the integral of `Φ`, `W` and `|det|^s` converges, put
`a(g) = Φ(g) |det g|^s`. Then `a(x g) = a(g)` for `x ∈ K`. The lemma
`Langlands.GodementJacquet.leftAverage_integral` (module `LeftAveraging`) shows
that the integrand of `f` is integrable and that

`∫ a f dμ = c · μ(K) · ∫ a W dμ = ∫ a W dμ`.

So `f` converges wherever `W` does, on the same right half-plane, and its shifted
integral has the same values there. The rational function `R` is therefore a
shifted rational value of `(Φ, f)`, with half-plane bound the maximum of the
convergence and continuation bounds.

### `Langlands.GodementJacquet.Padic.jpssI3_le_jpssI2`

For smooth `σ` and any `ℓ`:

`Padic.jpssI3 F ψ σ ℓ ≤ Padic.jpssI2 F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule) (glModelRepresentation ψ n σ ℓ)`.

Proof: both sides are Laurent spans of the value sets, and
`Submodule.span_mono` applies to `whittakerRationalValues_subset`.

## Integration note

The local topology and measure instances have explicit averaging-specific names
to permit importing this module together with `GodementJacquet.AnalyticData`;
their values and mathematical assertions are unchanged. This is a helper for
the actual coefficient-model comparison; it does not establish convergence of
Whittaker integrals that have not already been supplied with convergence.
