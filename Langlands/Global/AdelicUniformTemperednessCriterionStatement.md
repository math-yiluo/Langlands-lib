# A uniform temperedness criterion on Siegel sets

Module `Langlands.Global.AdelicUniformTemperednessCriterionStatement`, namespace
`Langlands.Global`. It states one proposition, `UniformTemperednessCriterionStatement`, and
proves nothing.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.10–I.2.12, printed
  pp.30–35 (the difference `φ − φ_P` of a function of uniform moderate growth and its constant
  term is rapidly decreasing where the roots outside `P` are large); Lemma I.4.1, printed p.49
  (an automorphic form is bounded on a Siegel set by the exponents of its constant terms); the
  Lemma of I.4.2, printed p.51 (bounds for exponential polynomials in terms of finitely many
  values).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering): Lemma 3.1, pp.10–11
  (the extension of MW I.2.10 to arbitrary standard parabolics, with polynomial weights);
  Lemma 3.2, p.11 (temperedness on Siegel sets, `|φ(exp X ω)| ≪ e^{ρ(X)} (1 + ‖X‖)^d` for `ω`
  in a compact set and `X` in the closed chamber); Proposition 3.6, p.13 (an automorphic form is
  tempered if and only if the exponents of its constant terms along all standard parabolics are
  subunitary; the sufficiency is MW I.4.1; the ray bound (3.4) is used in the proof of the
  necessity); the proof of Proposition 4.1, p.17 ("Lemma I.4.1 of [MW] holds uniformly for a set
  of automorphic forms which is bounded in a space of functions with given moderate growth and
  whose constant terms uniformly satisfy the assumption of that lemma").
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`: §4, printed p.315 (polynomial
  exponential functions, the difference-operator characterization (5) and the extrapolation
  formula (7), after MW I.4.2).

Provenance: derived. The statement is the uniform version of the sufficiency in Delorme's
Proposition 3.6 that Delorme uses in the proof of his Proposition 4.1, in the Siegel-set form of
`EisensteinUniformTemperednessStatement`. Delorme states the uniformity in words and attributes
it to the proof of MW I.4.1. The hypotheses are formulated with the Library's predicates
`IsUniformGrowthFamily` (module `Langlands.Global.AdelicEisensteinUnitaryGrowthStatement`) and
`StandardParabolicFamily.HasSubunitaryShiftEquations` (module
`Langlands.Global.AdelicEisensteinUnitaryExponentStatement`).

## The statement

Let `F : Type` be a number field and `G` a connected reductive group over `F`, with
`rho : G → GL_N` a closed matrix embedding (`IsClosedSubgroup rho`) and the smooth structure
data `hsmooth`, `hcalc`. Let `f : Idx → FinitePlotSmoothRationalFunctions F G` be a family of
continuous left `G(F)`-invariant functions with smooth archimedean slices, `S ⊆ Idx`, `L` an
open subgroup of `G(𝔸_f)`, `R : ℝ` and `m : ℕ`. Assume:

1. `IsUniformGrowthFamily rho hsmooth hcalc L R f S`: every `f x`, `x ∈ S`, is right
   `L`-invariant, and every derivative `u · f x` is bounded by `M_u ‖g‖^R` with `M_u`
   independent of `x ∈ S`;
2. for every standard parabolic family `𝓕` of `G`, every standard index `J` and every `x ∈ S`,
   the constant term `𝓕.constantTerm J (f x)` satisfies
   `𝓕.HasSubunitaryShiftEquations J m`: along every dominant point `a` of `𝔄_J` it is
   annihilated by a difference operator `∏_{k<m} (L_a − w_k)` with `|w_k| ≤ δ_{P_J}(a)^{1/2}`.

Conclusion: there is `k : ℕ` such that for every algebraic Siegel setup `(T, i, ν, T₀, j)`
(`IsSiegelAlgebraicSetup`), every threshold `t : ℝ≥0ˣ` and every compact `Ω ⊆ G(𝔸)` there is
`B` with

`‖f x (z · b · ω)‖ ≤ B · siegelModulus(b)^{1/2} · adelicLogHeight(z · b · ω)^k`

for all `x ∈ S`, `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`), `b` in the weak
simple-root chamber `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t` (mapped to
`G(𝔸)` by `positiveMap`) and `ω ∈ Ω`. The exponent `k` depends on the family but not on the
setup, the threshold or `Ω`; `B` depends on all data but not on `x ∈ S`.

## Why it is true

The following outline explains the statement; it is not proved here. It uses the half-modulus
comparison: on positive points of the split component of `P_J`, `δ_{P_J}` is the product of the
positive roots with the dimensions of their weight spaces. Fix the standard family of the setup,
with maximal split torus `T`, and write `δ_T(t) = ∏_{β ∈ Φ⁺} |β(t)|^{m_β}` for positive points
`t` of `T`. A point `z · b` of the conclusion is a positive point `t` of `T` whose simple-root
coordinates `log |α(t)|` are bounded below by a constant depending on the threshold, and
`siegelModulus(b) = δ_T(t)`. Write `C_J` for the constant term along `P_J` and `‖t‖` for the
size of the logarithmic coordinates of `t`.

*Ingredients.*

- *Shift equations along `T`.* For `J' ⊆ J` and a positive point `t` of `T` on which the simple
  roots in `J` are trivial and the other simple roots are at least one, `t` lies in the split
  component of `P_{J'}`, and the half-modulus comparison gives `δ_{P_{J'}}(t) = δ_T(t)`. So the
  hypothesis gives an annihilator `∏_{k<m} (L_t − w_k)` of `C_{J'} f x` with
  `|w_k| ≤ δ_T(t)^{1/2}`.
- *Recurrence bound.* If a sequence `u(0), u(1), …` is annihilated by `∏_{k<m} (T − w_k)` with
  all `|w_k| ≤ 1` and `m ≥ 1`, then `|u(q)| ≤ C_m (q + 1)^{m−1} max_{j<m} |u(j)|` with `C_m`
  depending only on `m` (for instance `C_m = m 2^m`). Coinciding roots are allowed. In the
  application the values along the powers of `t` are first divided by `δ_T(t)^{q/2}`, which puts
  the roots in the closed unit disc.
- *Growth.* Uniform moderate growth gives, for every compact `Ω`, a bound
  `|C_J f x (u ϖ)| ≪ e^{K ‖u‖}` for positive `u`, `ϖ ∈ Ω` and `x ∈ S`. Averaging over the compact
  quotients `U_J(F) \ U_J(𝔸)` gives the same kind of bound for the derivatives of the
  differences `C_J f x − C_{J ∖ α} f x`, with a rate `K` that depends neither on `Ω` nor on the
  order of the derivative.

*Induction.* By strong induction on the number of simple roots in `J`: for every compact `Ω` and
every lower bound `−θ` on the simple-root coordinates there is `C` with

`|C_J f x (t ϖ)| ≤ C (2m ‖t‖ + 3)^{2m} δ_T(t)^{1/2}`

for all `x ∈ S`, all such `t` and `ϖ ∈ Ω`.

- If every coordinate of `t` at a root in `J` is at most `θ + 2`, write `t = s^q t₀` with `s`
  a point on which the roots in `J` are trivial and the other simple roots are at least one,
  `q` at most a constant multiple of `‖t‖ + 1`, and `t₀` in a bounded set. Extrapolate `C_J f x` along the powers of `s` from
  `m` sample points whose coordinates are bounded in terms of `θ` and `m`. The recurrence
  bound and the growth bound at the sample points give the claim.
- Otherwise let `α₀ ∈ J` have the largest coordinate `ρ > θ + 2`, and split
  `C_J f x = h + C_{J ∖ α₀} f x`. The second term is bounded by the induction hypothesis. The
  difference `h` is annihilated along the same directions by the product of the two operators
  of order `m`, so by an operator of order `2m`. It is extrapolated from sample points `u` whose
  `α₀`-coordinate is at least `ρ − 1` and whose coordinates are all bounded by `ρ + θ + 2`. At
  those points `h = C_J f x − C_{P_{α₀}}(C_J f x)`, where `P_{α₀}` is the maximal parabolic
  omitting `α₀` (`StandardParabolicFamily.constantTerm_constantTerm`), and MW I.2.10 (in the
  Library, `adelicMaximalUnipotentDecay`) bounds `|h(u ϖ)|` by an arbitrary negative power of
  `|α₀(u)|` times the derivative bounds. As the rate `K` is fixed in advance, a large enough
  power absorbs the growth `e^{O(ρ)}` uniformly in `ρ`.

For `J` the index of `G` the constant term is `f x` itself. On the points `z b ω` the size
`2m ‖t‖ + 3` is bounded by a multiple of the logarithmic height `σ(z b ω)` (the case `N = 0`,
where `G(𝔸)` is a point, is separate). This gives the conclusion with `k = 2m` for every
setup; only `B` depends on the setup, the threshold and `Ω`. The proposition itself asks only
for some `k` that does not depend on the setup.

## Use

`eisensteinUniformTemperedness_of_criterion` (module
`Langlands.Global.AdelicEisensteinUniformTemperednessReduction`) derives
`EisensteinUniformTemperednessStatement` from this statement, `EisensteinUnitaryUniformGrowthStatement`
and `EisensteinUnitaryExponentStatement`.

## Scope

Only the functions themselves are bounded; derivatives are not. No exponent decomposition or
square-integrability is asserted. Nothing is proved here.
