# Transport of center annihilators through normalized Levi restrictions

The analytic lemma `IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero_of_levi` transports
annihilation of normalized inducing restrictions to normalized restrictions of the intertwining
integral. The module also proves
`IntertwiningUniformCenterIdealReductionStatement` (theorem
`intertwiningUniformCenterIdealReduction`). It shows that `LeviRestrictionCenterTransferStatement`
and `IntertwiningStabilizerModulusStatement` imply `IntertwiningUniformCenterIdealStatement`.

## The core lemma

`IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero_of_levi` fixes an ambient central
operator `z` and an enveloping operator `y` on `M'(F_∞)`. The normalized target restriction
intertwines `z` with `y` on left `V(F_∞)`-invariant plot-smooth functions (`hy1`), and `y`
annihilates every normalized inducing restriction of `φ` (`hkill`). Fix a parameter `λ` and a
finite adelic point `b` at which the slice `T_b` of `T = M(w, λ)φ` is plot-smooth. The domination
hypothesis `hdom` gives a real function `bd` on the quotient for each compact `C ⊆ G(𝔸)`.
It is integrable for `intertwiningMeasure` and bounds the norm of the intertwining integrand at
every `g ∈ C`, pointwise on the quotient. The lemma proves `z · T_b = 0`. Fix `a ∈ G(F_∞)`
and put `g = (a, b)`.

1. *Reduction to `M'(F_∞)`.* The core lemma assumes that `φ` is left invariant under
   `U(𝔸)M(F)` (`parabolicQuotientSubgroup`). Then `T` is left invariant under `V(𝔸)M'(F)` by the
   Library theorem `IsIwasawaCompact.intertwiningOperator_leftInvariant` (module
   `AdelicIntertwiningLeftInvariance`), so `T_b` is left invariant under `V(F_∞)`. The function
   `Ψ(m) = δ_Q(m)^{-1/2} T_b(m a)` on `M'(F_∞)` is plot-smooth
   (`parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions`,
   `comp_affinePointsTarget_mem_infinitePlotSmoothFunctions`). The first transfer property gives
   `(y · Ψ)(1) = (z · T_b)(a)`. It suffices to show `y · Ψ = 0`.
2. *Weak formulation.* Let `ν` be the right Haar measure `haar.inv` on `M'(F_∞)`. By
   `eq_zero_of_forall_integral_compactPlotSmooth` it suffices that `∫ (y Ψ) ψ dν = 0` for every
   compactly supported plot-smooth `ψ`. By `exists_envelopingAction_transpose` this is
   `∫ Ψ ϑ dν` with `ϑ = T ψ` compactly supported and plot-smooth.
3. *Restriction formula.* By `IsIwasawaCompact.intertwiningOperator_levi_mul` (the Library's
   `IsIwasawaCompact.intertwiningOperator_normalized_levi` with its Haar hypothesis supplied by the
   stabilizer modulus identity), `Ψ(m) = δ_P(c(m))^{-1/2} m_Q(g)^{-wλ} ∫ F₀(m, r) dr`, with
   `F₀(m, r) = φ(c(m) h_r) m_P(h_r)^λ` and `h_r = w⁻¹ v_r g`.
4. *Fubini.* The function `(m, r) ↦ ϑ(m) δ_P(c(m))^{-1/2} F₀(m, r)` is integrable
   (`IsIwasawaCompact.integrable_leviIntegrand_prod`): `hdom`, applied to the compact image of
   `tsupport (ϑ · δ_P(c(·))^{-1/2})` under `m ↦ q(l'(m)) g`, gives the integrable majorant `bd`. Hence
   `∫ Ψ ϑ dν = m_Q(g)^{-wλ} ∫_r ∫_m ϑ(m) δ_P(c(m))^{-1/2} F₀(m, r) dν dr`.
5. *Fibres.* For fixed `r`, write `h_r = (a_r, b_r)`. Then `F₀(m, r) = m_P(h_r)^λ · φ_{b_r}(c(m) a_r)`,
   where `φ_{b_r}` is the slice of `φ` at `b_r`. The inner integral is `m_P(h_r)^λ ∫ Φ_r ϑ dν` with
   `Φ_r(m) = δ_P(c(m))^{-1/2} φ_{b_r}(c(m) a_r)`. By the transpose this is
   `m_P(h_r)^λ ∫ (y Φ_r) ψ dν`. The inducing annihilation hypothesis applies to this plot-smooth
   normalized restriction and gives `y Φ_r = 0`.

So every fibre integral vanishes, `∫ Ψ ϑ dν = 0`, and `y · Ψ = 0`.

## Application to the two-parabolic transfer

`IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero` specializes the core lemma to an
operator `z` annihilating the slices of `φ` and a Levi operator `y` realizing `z` on both normalized
restrictions. Each inducing slice is left invariant under `U(F_∞)`, so the inducing transfer
identity and the annihilation by `z` supply `hkill`.

`intertwiningUniformCenterIdealReduction` chooses `R₀` from `intertwiningAbsoluteConvergence` and
`J` from the center-finiteness clause of `IsAutomorphicFunctionOn` for `φ`. It derives the
instances for `P`, `Q`, `V` and `M'` using local finite type
from the closed immersions (`IsClosedSubgroup.locallyOfFiniteType`), and affineness and smoothness
of `M'` from its connected reductivity, which `IsRationalLeviSubgroup` provides. It chooses a smooth
structure on `M'` (`IsConnectedReductive.exists_smoothOfRelativeDimension`) and its commutator datum
(`adelicDifferentialCommutator_of_smooth`). It takes the parabolic and Levi properties of `P` from
the root presentation. For each `z ∈ J` it obtains `y` from the first premise. The domination
hypothesis comes from `intertwiningAbsoluteConvergence` applied to the singleton parameter set
`{λ}` in linear coordinates (`exists_complexParameterEquiv`). The core lemma concludes.

## Relation to the source

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), proof of the Lemma in §8.2, p. 222, transport a finite-codimensional ideal of `𝔷^M` to the
normalized restrictions of `M(w, λ)φ` by (6.5) and pull it back to `𝔷`. The core lemma implements
the step through (6.5) weakly, against compactly supported functions on `M'(F_∞)`, by integration
by parts and Fubini's theorem. The two-parabolic application uses a single transferred operator
for both parabolics and therefore takes an ideal annihilating `φ` as the uniform ideal.
