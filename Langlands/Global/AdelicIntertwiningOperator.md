# Intertwining operators on actual adelic points

Module `Langlands.Global.AdelicIntertwiningOperator` defines the global
intertwining integral and the operator
`[M(w, λ)φ]_{wλ}(g) = ∫ φ_λ(w⁻¹ v g) dv` for parabolic subgroups of an
affine group scheme over a number field, together with the parameter map
`λ ↦ wλ` and the conjugation data presenting an element of `W(P, Q)`. It is a
definition module; its only lemmas are the membership description
`mem_intertwiningRationalSubgroup_iff`, the formula `weylParameter_tmul` and
the discreteness `isDiscrete_intertwiningRationalSubgroup` used to build the
quotient measure.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  chapter file `06.1_pp_78_100_Definitions.pdf`, II.1.6, printed pp.87–88:
  for standard Levis `M`, `M'` of standard parabolics `P`, `P'` with
  unipotent radicals `U`, `U'`, and `w ∈ G(k)` with `wMw⁻¹ = M'`,
  `(M(w, π)φ_π)(g) = ∫_{(U'(k) ∩ wU(k)w⁻¹) \ U'(𝔸)} φ_π(w⁻¹ u g) du`
  whenever the integral converges. The Remark after the definition says that
  this equals the integral over `(U'(𝔸) ∩ wU(𝔸)w⁻¹) \ U'(𝔸)`, because
  `(U'(k) ∩ wU(k)w⁻¹) \ (U'(𝔸) ∩ wU(𝔸)w⁻¹)` has volume `1`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`. §2.1
  (journal p.190) defines `W(P, Q)` as the set of cosets `wM_P(F)`,
  `w ∈ G(F)`, with `wM_Pw⁻¹ = M_Q`. §2.2 (p.191) defines
  `M(w, λ) : 𝒜_P → 𝒜_Q` by
  `[M(w, λ)φ]_{wλ}(g) = ∫_{(wU_Pw⁻¹ ∩ U_Q)(𝔸) \ U_Q(𝔸)} φ_λ(w⁻¹ u g) du`,
  with the Haar measure on `V(𝔸)` normalized by `vol(V(F) \ V(𝔸)) = 1` for
  every unipotent `V` (footnote to the definition). Here `[ψ]_μ(g) = ψ(g) m_Q(g)^μ`.

## Existing objects used

- `IsIwasawaCompact p K`, `hK.heightPower` and `hK.parameterTwist`
  (modules `Langlands.Global.AdelicIwasawaHeight` and
  `Langlands.Global.AdelicEisensteinSeries`): `m_P(g)^λ` and
  `φ_λ(g) = φ(g) m_P(g)^λ`.
- `parabolicUnipotentImage F p iU`, the subgroup `U(𝔸)` of `G(𝔸)`
  (module `Langlands.Global.AdelicParabolicQuotient`).
- `AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)` and
  `AdelicSubgroupPoints.rationalSubgroup`, the subgroup `V(𝔸)` of `G(𝔸)` for
  `j : V → G` and its rational points `V(F)`;
  `AdelicSubgroupPoints.normalizedHaarMeasure`, the Haar measure of `V(𝔸)`
  divided by the mass of `V(F) \ V(𝔸)`; `isClosed_adelicPoints_range` and
  `isDiscrete_rationalSubgroup` (module
  `Langlands.Global.AdelicSubgroupHaarMeasure`).
- `LeftCosetSpace Γ` and `LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν`, the
  quotient `Γ \ H` by a discrete subgroup with the measure induced by `ν`
  through a chosen Borel fundamental domain (module
  `Langlands.Global.LeftCosetFundamentalDomain`).
- `G.innerIso w`, conjugation `x ↦ w x w⁻¹` by a point `w` of `G` over the
  base (module `Langlands.GroupScheme.InnerAutomorphism`), and
  `innerAdelicPoint F G w`, the image of `w` in `G(𝔸)`, which is a rational
  point (`innerAdelicPoint_eq_rational`, module
  `Langlands.Automorphic.GroupSchemeConstantTermConjugation`).
- `characterRestrict` and `ComplexCharacterParameter F P = ℂ ⊗[ℤ] X^*(P)`
  (module `Langlands.Global.AdelicComplexParameters`).

## Definitions

Let `p : P → G`, `q : Q → G` be the parabolics, `iU : U → P`,
`iV : V → Q` their unipotent radicals, `l : M → P`, `l' : M' → Q` Levi
subgroups, `w` a point of `G` over `Spec F`, and `c : M' → M`.

- `weylParameter l c π'`, for a further map `π' : Q → M'`, is the
  `ℂ`-linear map `X^*(P) ⊗ ℂ → X^*(Q) ⊗ ℂ` given on characters by
  `χ ↦ χ ∘ l ∘ c ∘ π'` (`weylParameter_tmul`). This is the source's `wλ`.
- `IsWeylConjugation p l q l' w c` says that `c` is an isomorphism and
  `p ∘ l ∘ c = Int(w)⁻¹ ∘ q ∘ l'`, i.e. `l(c(m')) = w⁻¹ l'(m') w` in `G`.
  So `w⁻¹ M' w = M`, i.e. `wMw⁻¹ = M'`, and `c` is conjugation by `w⁻¹`.
  The pair `(w, c)` presents an element of the source's `W(P, Q)`; the
  coset `wM(F)` is not formed.
- `intertwiningRationalSubgroup F p iU j w`, for `j : V → G` and
  `w ∈ G(𝔸)`, is the subgroup `V(F) ∩ w U(𝔸) w⁻¹` of `V(𝔸)`: the rational
  points `v` of `V` with `w⁻¹ v w ∈ U(𝔸)`
  (`mem_intertwiningRationalSubgroup_iff`). It is discrete because `V(F)`
  is (`isDiscrete_intertwiningRationalSubgroup`).
- `intertwiningMeasure F p iU j w`, for a closed immersion `j`, is the
  measure on `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` induced, through a fundamental
  domain, by `normalizedHaarMeasure` of `V(𝔸)`.
- `hK.intertwiningIntegrand iU j w φ λ g x = φ_λ(w⁻¹ v g)` for the
  representative `v ∈ V(𝔸)` of the class `x` chosen by `Quotient.out`, with
  `w` acting through `innerAdelicPoint`.
- `hK.intertwiningIntegral iU j w φ λ g` is the Bochner integral of the
  integrand against `intertwiningMeasure`, so `0` where the integrand is not
  integrable.
- `hK.intertwiningOperator hK' iU l iV c π' w φ λ g =
  m_Q(g)^{-wλ} · hK.intertwiningIntegral iU (iV ≫ q) w φ λ g`, where
  `hK' : IsIwasawaCompact q K` gives `m_Q` and `wλ = weylParameter l c π' λ`.
  Thus `[M(w, λ)φ]_{wλ}` is the intertwining integral, as in BL.

## Correspondence with the source

- The quotient. The definition integrates over the discrete quotient
  `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, as MW do. For rational `w` and a closed
  subgroup `U`, `G(F) ∩ wU(𝔸)w⁻¹ = wU(F)w⁻¹`, so the subgroup is MW's
  `V(F) ∩ wU(F)w⁻¹`. By MW's Remark the integral equals BL's integral over
  the adelic quotient `(wUw⁻¹ ∩ V)(𝔸) \ V(𝔸)`. Neither identification is
  proved here.
- The measure. `normalizedHaarMeasure` is Haar measure on `V(𝔸)` scaled by
  the inverse mass of `V(F) \ V(𝔸)`. For a unipotent `V` this quotient is
  compact, so the scaled measure gives it volume `1`, which is BL's
  footnote and MW's normalization.
- Representatives. For `φ` left `U(𝔸)`-invariant, `φ_λ` is left
  `U(𝔸)`-invariant too, and for `γ ∈ V(F) ∩ wU(𝔸)w⁻¹` one has
  `w⁻¹ γ v g = (w⁻¹ γ w) w⁻¹ v g` with `w⁻¹ γ w ∈ U(𝔸)`. So for the source's
  `φ ∈ 𝒜_P` the integrand does not depend on the representatives. The
  definition uses chosen representatives so that it needs no hypothesis
  on `φ`.
- The parameter `wλ`. BL's `wλ ∈ 𝔛_Q` is `m' ↦ (w⁻¹ m' w)^λ` on
  `M'(𝔸)`, through `X^*(Q) = X^*(M')`. With `π'` a retraction of `l'`
  (`l' ≫ π' = 𝟙`, the Levi projection `Q → Q/V ≅ M'`) the character
  `χ ∘ l ∘ c ∘ π'` restricts on `M'` to `m' ↦ χ(w⁻¹ m' w)`. Any two such
  retractions give the same character of `Q`, because characters of `Q` are
  trivial on the unipotent `V` and `Q = M'V`. The definition accepts any
  `π'`; the retraction property is a hypothesis of the statements that need
  it.

## Scope

No convergence, holomorphy, automorphy, continuation or functional equation
is asserted here, and there is no hypothesis on `P`, `Q`, `w`, `c`, `π'` or
`K` beyond those needed to form the measure. Absolute convergence is the
separate statement `Langlands.Global.IntertwiningAbsoluteConvergenceStatement`.
The set `W(P, Q)` itself and the fact that `M(w, λ)` depends only on the
double coset `M'(F) w M(F)` (MW II.1.6 (i)) are not formalized.
