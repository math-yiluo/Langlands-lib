# Proof of the uniform center ideal from the Levi transfer and the Haar factor

Module `Langlands.Global.AdelicIntertwiningCenterIdealReduction` proves
`IntertwiningUniformCenterIdealReductionStatement` (theorem
`intertwiningUniformCenterIdealReduction`). It shows that `LeviRestrictionCenterTransferStatement`
and `IntertwiningStabilizerModulusStatement` imply `IntertwiningUniformCenterIdealStatement`. It
does not prove the two premises.

## Choice of the threshold and the ideal

For the data of the target, the threshold `R₀` is the one of the absolute convergence theorem
`intertwiningAbsoluteConvergence`. The ideal `J` is the one supplied by the center-finiteness clause
of `IsAutomorphicFunctionOn` for `φ`: an ideal of finite codimension in
`AdelicEnvelopingCenter F G hsmooth` that annihilates every plot-smooth infinite slice of `φ`.
So the uniform ideal of Bernstein–Lapid's §8.2 can be taken to be an ideal that annihilates `φ`.
This uses that the transfer in the first premise is one element `y` for both parabolics.

## The core lemma

`IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero` fixes a central `z` that annihilates the
slices of `φ`, an element `y` of the enveloping algebra of `M'(F_∞)` with the two transfer
properties of the first premise, a parameter `λ` for which the intertwining integrand has an
integrable majorant uniform on each compact set (hypothesis `hdom`: for every compact `C ⊆ G(𝔸)`
there is a real function `bd` on the quotient, integrable for `intertwiningMeasure`, with
`‖integrand of M(w, λ)φ at g‖ ≤ bd` for all `g ∈ C`), and a finite adelic point `b` at which the
slice `T_b` of `T = M(w, λ)φ` is plot-smooth. It proves `z · T_b = 0`. The core lemma does not
assume that `λ` is regular; the theorem below supplies `hdom` for every regular `λ` from absolute
convergence. Fix `a ∈ G(F_∞)` and put `g = (a, b)`.

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
   second premise), `Ψ(m) = δ_P(c(m))^{-1/2} m_Q(g)^{-wλ} ∫ F₀(m, r) dr`, with
   `F₀(m, r) = φ(c(m) h_r) m_P(h_r)^λ` and `h_r = w⁻¹ v_r g`.
4. *Fubini.* The function `(m, r) ↦ ϑ(m) δ_P(c(m))^{-1/2} F₀(m, r)` is integrable
   (`IsIwasawaCompact.integrable_leviIntegrand_prod`): `hdom`, applied to the compact image of
   `tsupport ϑ` under `m ↦ q(l'(m)) g`, gives the integrable majorant `bd`. Hence
   `∫ Ψ ϑ dν = m_Q(g)^{-wλ} ∫_r ∫_m ϑ(m) δ_P(c(m))^{-1/2} F₀(m, r) dν dr`.
5. *Fibres.* For fixed `r`, write `h_r = (a_r, b_r)`. Then `F₀(m, r) = m_P(h_r)^λ · φ_{b_r}(c(m) a_r)`,
   where `φ_{b_r}` is the slice of `φ` at `b_r`. That slice is plot-smooth and left invariant under
   `U(F_∞)`. The inner integral is `m_P(h_r)^λ ∫ Φ_r ϑ dν` with
   `Φ_r(m) = δ_P(c(m))^{-1/2} φ_{b_r}(c(m) a_r)`. By the transpose this is
   `m_P(h_r)^λ ∫ (y Φ_r) ψ dν`. The second transfer property gives
   `y Φ_r = δ_P(c(·))^{-1/2} (z φ_{b_r})(c(·) a_r)`, and `z φ_{b_r} = 0` by hypothesis.

So every fibre integral vanishes, `∫ Ψ ϑ dν = 0`, and `y · Ψ = 0`.

## The theorem

`intertwiningUniformCenterIdealReduction` unpacks `IsAutomorphicFunctionOn` for `φ` and chooses
`R₀` and `J` as above. It derives the instances for `P`, `Q`, `V` and `M'`: locally of finite type
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
normalized restrictions of `M(w, λ)φ` by (6.5) and pull it back to `𝔷`. The implemented proof
instead uses one transferred operator for both parabolics. It checks the transfer weakly, against
compactly supported functions on `M'(F_∞)`, by integration by parts and Fubini's theorem. This
avoids differentiating the noncompact intertwining integral, which would need dominating
functions for derivatives of every order with one threshold. The ideal is an ideal annihilating
`φ`, chosen before `λ`.
