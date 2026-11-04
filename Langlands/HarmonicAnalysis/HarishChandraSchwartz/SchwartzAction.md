# The operators `π(f)`, `f ∈ C(G)`, and the character `θ_π` (III.7)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published modules `TemperedPairing`
(`HasTemperedGrowth`, `hasTemperedGrowth_iff`, `Space.temperedPairing`,
`Space.integrable_mul`) and, through it, `L2` (`L2Weights`) and `Basic` (`Space`, `Level`,
`Space.ofLevel`, `Space.continuous_ofLevel`, `Space.mkCLM`, `Level.isBiInvariant`,
`mem_schwartzSubmodule_iff`); `TestFunctions` (`ofSchwartzBruhat`);
`Langlands.HarmonicAnalysis.SmoothWeakIntegral` (`HasIntegral`, `integrableSubmodule`,
`integralLinear`, `integralLinear_spec`, `integralLinear_eq`, `integralLinear_eval`);
`Langlands.Representation.MatrixCoefficient.LawsProof` (`matrixCoefficient_isLocallyConstant`);
`Langlands.Representation.Smooth.Contragredient.LawsProof` and, through the imports, the
smooth contragredient (`SmoothDual`, `smoothContragredient`,
`smoothBidual_injective_of_compact_cofinal`, `smoothBidual_surjective_of_compact_cofinal`,
`smoothDualFixedRestriction`, `smoothDualFixedRestriction_bijective`);
`Langlands.LinearAlgebra.FiniteRankTrace` (`finiteRankEnd`, `mem_finiteRankEnd_iff`,
`FiniteRankEnd.onSubspace`, `FiniteRankEnd.trace`, `FiniteRankEnd.trace_eq_subspace`); and
`Langlands.Representation.Hecke.IntegratedAction` (`Hecke.integratedAction`,
`Hecke.integratedAction_dual`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- III.2 (printed p. 265, PDF p. 31): `C^w_lisse(G)` is the space of `f ∈ C_lisse(G)` with
  `|f(g)| ≤ c Ξ(g) (1 + σ(g))^r` for some `c > 0`, `r ∈ ℝ` and all `g`;
  `A^w(G) = A(G) ∩ C^w_lisse(G)`, and an admissible `(π, V)` is tempered if
  `A(π) ⊂ A^w(G)`, where `A(π)` is spanned by the coefficients `g ↦ ⟨π(g)v, v̌⟩`,
  `v ∈ V`, `v̌ ∈ V̌`.
- III.7 (printed p. 273, PDF p. 39), first paragraph: for `(π, V)` admissible tempered,
  `v ∈ V`, `v̌ ∈ V̌` and `f ∈ C(G)`, the integral `∫_G f(g) ⟨π(g)v, v̌⟩ dg` converges
  absolutely; "on vérifie qu'il existe un unique élément, noté `π(f)v`, de `V`, tel que pour
  tout `v̌`, l'intégrale ci-dessus soit égale à `⟨π(f)v, v̌⟩`. Cela définit un opérateur
  `π(f) ∈ End_ℂ(V)`. On vérifie que `π(f_1 ∗ f_2) = π(f_1)π(f_2)` pour tous
  `f_1, f_2 ∈ C(G)`. Comme `π` est admissible, `π(f)` est de rang fini pour tout
  `f ∈ C(G)`. On pose `θ_π(f) = trace π(f)`. La forme linéaire ainsi définie sur `C(G)`
  est continue."

The pairing `⟨π(g)v, v̌⟩` is `ℓ.val (ρ g v)` for `ℓ : SmoothDual ρ`.

## Scope: abstract data and explicit hypotheses

`G` is a topological group with a compact open subgroup (`[Nonempty (CompactOpenSubgroup G)]`),
`[MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]`, and `μ` is a left
invariant measure on `G` (`[μ.IsMulLeftInvariant]`). The weights `Ξ, σ : G → ℝ` are
arbitrary and enter through the hypothesis `hw : L2Weights μ Ξ σ` of `L2` (`Ξ > 0`,
`σ ≥ 0` and Lemma II.1.5, `∫_G Ξ^2 (1 + σ)^{-d} dμ < ∞` for some `d`); none of this is
proved here for Waldspurger's `Ξ`, `σ` and Haar measure. The representation is a
`Representation ℂ G V` on a complex vector space without topology, with the hypotheses
`hρ : IsAdmissible ρ` (smooth, with finite-dimensional `V^K` for every open subgroup `K`)
and `hT : HasTemperedCoefficients Ξ σ ρ`.

`HasTemperedCoefficients` asks only for the growth bound on each coefficient. Since tempered
growth is preserved under sums and scalar multiples (`HasTemperedGrowth.add`,
`HasTemperedGrowth.smul` in `TemperedPairing`), this is the same as the growth bound on the
span `A(π)`; the bi-invariance part of `C^w_lisse(G)` is not part of the hypothesis (the
integrals only use that coefficients of a smooth representation are continuous,
`continuous_coefficient`). With Waldspurger's `Ξ` and `σ` it is the condition
`A(π) ⊂ A^w(G)` of III.2 up to that bi-invariance; this identification is not formalized.
The notion is not compared with the Library's `IsTemperedModCenter` (coefficients in
`L^{2+ε}` modulo the center), which is a different definition.

## Definitions

- `HasTemperedCoefficients Ξ σ ρ : Prop`: for all `v : V` and `ℓ : SmoothDual ρ`,
  `HasTemperedGrowth Ξ σ (fun g => ℓ.val (ρ g v))`.
- `coefficientPairing hw hρ hT v ℓ : Space Ξ σ →L[ℂ] ℂ`: `f ↦ ∫_G f(g) ℓ(ρ(g) v) dμ(g)`
  (`Space.temperedPairing` applied to the coefficient).
- `dualIntegral hw hρ hT f v : Module.Dual ℂ (SmoothDual ρ)` and
  `dualIntegralSmooth hw hρ hT f v : SmoothDual (smoothContragredient ρ)`: the linear form
  `ℓ ↦ ∫_G f(g) ℓ(ρ(g) v) dμ(g)` on the smooth dual, and the same form as a smooth vector
  of the smooth contragredient of the smooth dual.
- `integrand hw hρ hT f : V →ₗ[ℂ] SmoothWeakIntegral.integrableSubmodule ρ μ`:
  `v ↦ (g ↦ f(g) • ρ(g) v)`, a weakly integrable function.
- `actionEnd hw hρ hT f : Module.End ℂ V`: the weak integral of `integrand` (an auxiliary
  definition), and `schwartzAction hw hρ hT : Space Ξ σ →ₗ[ℂ] Module.End ℂ V`: `f ↦ π(f)`.
- `finiteRankSchwartzAction hw hρ hT : Space Ξ σ →ₗ[ℂ] finiteRankEnd V`: `π(f)` as a
  finite-rank endomorphism.
- `levelAction hw hρ hT K f : Module.End ℂ (fixedVectors ρ K.toSubgroup)`: for
  `f : Level Ξ σ K` (`f ∈ C_K`), the restriction of `π(f)` to `V^K`, viewed as an
  endomorphism of `V^K`.
- `schwartzCharacter hw hρ hT : Space Ξ σ →L[ℂ] ℂ`: `θ_π(f) = trace π(f)`, the trace of
  the finite-rank endomorphism `π(f)`.

## Results

- `continuous_coefficient`: coefficients of a smooth representation are continuous;
  `exists_nu_coefficient_ne_top`: under `HasTemperedCoefficients` some seminorm
  `ν_{-r}` of each coefficient is finite; `integrable_coefficient`: `f(g) ℓ(ρ(g) v)` is
  integrable for `f ∈ C(G)` (the absolute convergence in III.7).
- `integral_mul_coefficient_mul_left` and `dualIntegral_smoothContragredient`: for `f`
  left invariant under a subgroup `H` and `k ∈ H`, translating the coefficient by `k` (on
  the left) does not change the integral; equivalently `dualIntegral f v` is fixed by the
  contragredient action of `H`.
- `CompactOpenSubgroup.cofinal`: every open subgroup contains a compact open subgroup (the
  intersection with a given compact open subgroup); `ext_smoothDual`: smooth functionals
  separate the vectors of a smooth representation.
- `Space.exists_leftInvariant`, `Level.leftInvariant`: elements of `C(G)` (of `C_K`) are
  left invariant under some compact open subgroup (under `K`).
- `exists_hasIntegral` (existence in III.7): for `f ∈ C(G)` and `v ∈ V` there is `w ∈ V`
  with `ℓ(w) = ∫_G f(g) ℓ(ρ(g) v) dμ(g)` for every smooth functional `ℓ`, i.e.
  `SmoothWeakIntegral.HasIntegral ρ μ (fun g => f g • ρ g v) w`.
- `schwartzAction_eval`, `schwartzAction_eval_eq_coefficientPairing`: the defining property
  `ℓ(π(f) v) = ∫_G f(g) ℓ(ρ(g) v) dμ(g)`; `hasIntegral_schwartzAction` and
  `schwartzAction_eq_of_hasIntegral` (uniqueness in III.7): `π(f) v` is a weak integral of
  `g ↦ f(g) ρ(g) v` and every weak integral of it equals `π(f) v`.
- `continuous_schwartzAction_eval`: each matrix coefficient `f ↦ ℓ(π(f) v)` is continuous on
  `C(G)`.
- `schwartzAction_mem_fixedVectors`: if `f` is left invariant under `H`, then `π(f)` takes
  values in `V^H`; `range_schwartzAction_le`: for `f ∈ C_K`, the range of `π(f)` lies in
  `V^K`.
- `schwartzAction_mem_finiteRankEnd` (III.7, "comme `π` est admissible, `π(f)` est de rang
  fini"); `finiteRankSchwartzAction_val`; `levelAction_apply`.
- `trace_levelAction_eq_sum`: for a basis `b` of `V^K` and `K`-fixed smooth functionals
  `ℓ_i` restricting to the dual basis on `V^K`,
  `trace(π(f)|_{V^K}) = Σ_i ∫_G f(g) ℓ_i(ρ(g) b_i) dμ(g)`.
- `schwartzCharacter_apply`, `schwartzCharacter_ofLevel` (`θ_π(f) = trace(π(f)|_{V^K})`
  for `f ∈ C_K`); the continuity of `θ_π` (III.7, "la forme linéaire ainsi définie sur
  `C(G)` est continue") is part of `schwartzCharacter`, a continuous linear map.
- `schwartzAction_ofSchwartzBruhat` (under `[T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G]`, `[IsFiniteMeasureOnCompacts μ]` and continuity of `Ξ` and
  `σ`, needed for `ofSchwartzBruhat`): for a test function `f`,
  `π(f) = Hecke.integratedAction μ ρ hρ.1 f`, the published integrated action of
  `C_c^∞(G)`.

## Proof notes

Waldspurger leaves the construction to the reader ("on vérifie"). The Lean proof uses the
duality of admissible representations. Since `f ∈ C(G)` is left invariant under a compact
open subgroup `K` and `μ` is left invariant, the form `ℓ ↦ ∫ f(g) ℓ(ρ(g) v) dμ(g)` on the
smooth dual is fixed by `K` (substitute `g ↦ k g`), so it is a smooth vector of the smooth
contragredient of the smooth dual. For admissible `ρ` the canonical map from `V` to this
smooth bidual is surjective (`smoothBidual_surjective_of_compact_cofinal`), which gives a
vector `π(f) v` with the required pairings; it is unique because smooth functionals separate
points (`smoothBidual_injective_of_compact_cofinal`). Both duality theorems take the
cofinality of compact open subgroups as a hypothesis, which `CompactOpenSubgroup.cofinal`
derives from the existence of one compact open subgroup. The weak integral is then packaged
by `SmoothWeakIntegral.integralLinear`, and linearity in `f` follows by separation from the
linearity of `coefficientPairing`.

Finite rank: by the same substitution, `ρ(k) π(f) v` and `π(f) v` have the same pairings
for `k ∈ K`, so the range of `π(f)` lies in the finite-dimensional `V^K`.

Continuity of `θ_π`: by the universal property III.6 (1) of `C(G)` (`Space.mkCLM`) it
suffices to prove continuity on each level `C_K`. There the trace of `π(f)` equals the trace
on `V^K` (`FiniteRankEnd.trace_eq_subspace`), computed in a basis `b` of `V^K` as
`Σ_i ℓ_i(π(f) b_i)` with `ℓ_i` the `K`-fixed smooth functionals that restrict to the dual
basis (they exist by `smoothDualFixedRestriction_bijective`). Each summand is the continuous
functional `coefficientPairing` of `TemperedPairing` composed with `Space.ofLevel K`.

Compatibility with test functions: both operators have the pairings
`∫ f(g) ℓ(ρ(g) v) dμ(g)` (`Hecke.integratedAction_dual`), so they agree by separation.

## Open obligations

The identity `π(f_1 ∗ f_2) = π(f_1) π(f_2)` of III.7, the statement that `f φ ∈ C(G)` for
`f ∈ A(ω)`, `ω` square integrable and `φ ∈ C_c(G/G^1)` (from Corollary III.1.2), and
Proposition III.7.1 (the operators `π(p)`) are not formalized here. No topology on
`End_ℂ(V)` is introduced; the continuity in `f` proved here is that of the matrix
coefficients `f ↦ ℓ(π(f) v)` and of `θ_π`.
