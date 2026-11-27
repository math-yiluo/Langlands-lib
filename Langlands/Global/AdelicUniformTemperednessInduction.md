# The induction over standard parabolics in the uniform temperedness criterion

Module `Langlands.Global.AdelicUniformTemperednessInduction`, namespace
`Langlands.Global.StandardParabolicFamily`.

## Main result

`constantTerm_chamber_bound`. Let `𝓕` be a standard parabolic family with finitely many simple
roots `Δ`, `Fr : TorusFrame 𝓕` a coordinate frame, and `g x` (`x ∈ S`) continuous left
`G(F)`-invariant functions. Assume:

- (`hsm`, `hlev`) each `g x` is smooth on archimedean slices and right invariant under an open
  subgroup `L ≤ G(𝔸_f)`;
- (`hsh`) for all standard indices `J' ⊆ J`, the constant term `C_{J'} g x` satisfies torus shift
  equations of order `m` along `J` (`HasTorusShiftEquations`);
- (`hgr`) for every compact `Ω` there are `M, K` with
  `‖C_J g x (t ϖ)‖ ≤ M e^{K ‖t‖}` for all `J`, `x ∈ S`, positive `t` and `ϖ ∈ Ω`;
- (`hdgr`) there is `K` such that for every compact `Ω` and order `n` there is `M` bounding all
  derivatives of order `n` (in the directions of a fixed basis) of every step
  `C_J g x - C_{J ∖ α} g x` at `t k`, `k ∈ Ω`, by `M e^{K ‖t‖}`.

Here `‖t‖` is the norm of `Fr.crd t`. Then for every `J`, compact `Ω` and `θ ≥ 0` there is
`C ≥ 0` such that

`‖C_J g x (t ϖ)‖ ≤ C (2m ‖t‖ + 3)^{2m} δ_T(t)^{1/2}`

for every `x ∈ S`, every positive `t` whose root coordinates are all at least `-θ`, and every
`ϖ ∈ Ω`.

Also in the module: `positiveMap_id` (the positive map of `𝟙 T` is `torusPoint`),
`TorusFrame.norm_crd_le`, `TorusFrame.abs_root_le`, `TorusFrame.normCharacter_eq_exp`
(`|α(t)| = e^{step α · crd t α}`) and `pow_le_pow_two_mul`
(`(m x + 3)^m ≤ (2m x + 3)^{2m}` for real `x ≥ 0`).

## Proof

Strong induction on the number of simple roots in `J`, for all `Ω` and `θ` at once. Let `Λ` be
the constant of `exists_torusModulus_bounds` and put `B₀ = θ + 2`.

**Case 1: every root coordinate of `t` in `J` is at most `B₀`.** Then they all lie in
`[-θ, B₀]`. `norm_le_of_hasTorusShiftEquations_chamber` with `ρ = B₀`, `ρ' = θ` applies to the
shift equations of `C_J g x` along `J`. The points `u` of its hypothesis have
`‖u‖ ≤ B₀ + θ + 2`, where `hgr` gives `‖C_J g x (u ϖ)‖ ≤ M e^{K(B₀ + θ + 2)}`. This gives the
bound with the factor `(m ‖t‖ + 3)^m ≤ (2m ‖t‖ + 3)^{2m}`.

**Case 2: some root coordinate in `J` exceeds `B₀`.** Let `α₀ ∈ J` have the largest root
coordinate `ρ > B₀`. Write `C_J g x = h + C_{J ∖ α₀} g x` with the step
`h = C_J g x - C_{J ∖ α₀} g x`. The second term is bounded by the induction hypothesis for
`J ∖ α₀`.

The step satisfies shift equations of order `2m` along `J` (`HasTorusShiftEquations.sub`). Apply
`norm_le_of_hasTorusShiftEquations_chamber` to it with `ρ` and `ρ' = θ`. The points `u` of its
hypothesis satisfy:

- they lie in the weak simple-root chamber of threshold `b = e^{-(∑ step)(θ + 1)}`;
- their `α₀`-coordinate is at least `ρ - 1`;
- `‖u‖ ≤ ρ + θ + 2`.

`exists_constantTermStep_decay` (with `T₀ = T` and `rT = 𝟙`) at order `n₀` bounds `‖h(u ϖ)‖` by
`C_dec |α₀(u)|^{-n₀/[F:ℚ]} M_d e^{K_d ‖u‖}`, using `hdgr` on the enlarged compact set. Here `n₀`
is chosen so that `n₀ · step α / [F:ℚ] ≥ Λ + K_d + 1` for every `α`. The decay
`e^{-n₀ step(α₀)(ρ - 1)/[F:ℚ]}` then absorbs the growth `e^{Λ(ρ + θ + 1)} e^{K_d(ρ + θ + 2)}`,
uniformly in `ρ`. The resulting constant is independent of `t`, `x` and `ρ`. Summing over the
possible `α₀` gives the constant of the claim.

The rate `K_d` in `hdgr` does not depend on the compact set or the order `n`. This makes the
choice of `n₀` possible before the compact set `K'` of the decay estimate is known.

## Source

Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), Lemma I.4.1 and its
proof (printed pp.49–51) with I.2.10–I.2.12 (printed pp.30–35), and Delorme 2023, Proposition 3.6 and the proof of Proposition 4.1
(uniformity in the family) (registered as `moeglin-waldspurger-1995-spectral-decomposition` and
`delorme-2023-spectral-theorem-langlands`). The Lean proof replaces the exponent expansion by
shift equations, and the alternating sum of constant terms in the proof of Lemma I.4.1 (its
function (4) on p.50) by an induction on the number of simple roots of the index, applying the
I.2.10 estimate to one nested difference `C_J − C_{J ∖ α₀}` at a time.
