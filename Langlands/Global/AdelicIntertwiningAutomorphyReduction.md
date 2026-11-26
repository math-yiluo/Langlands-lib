# Uniform automorphy of intertwining integrals from two analytic parts: proof

Module `Langlands.Global.AdelicIntertwiningAutomorphyReduction` proves
`Langlands.Global.IntertwiningUniformAutomorphyReductionStatement.{u}` (module
`Langlands.Global.AdelicIntertwiningAutomorphyReductionStatement`) as the theorem
`Langlands.Global.intertwiningUniformAutomorphyReduction`, which is
`Langlands.Global.intertwiningUniformAutomorphy_of_analytic` with its two hypotheses:

`IntertwiningSmoothSlicesStatement.{u} → IntertwiningUniformCenterIdealStatement.{u} →
IntertwiningUniformAutomorphyStatement.{u}`.

Neither premise is proved here. Lean reports the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Notation: `T λ = hK.intertwiningOperator hK' iU l iV c π' w φ λ`, which is
`m_Q(g)^{-wλ} · I λ g` with `I λ = hK.intertwiningIntegral iU (iV ≫ q) w φ λ` the integral of
`x ↦ φ_λ(w⁻¹ x g)` over `Γ \ V(𝔸)`, `Γ = intertwiningRationalSubgroup F p iU (iV ≫ q) w`
(`V(F) ∩ wU(𝔸)w⁻¹`), for the measure `intertwiningMeasure` induced by the Haar measure of `V(𝔸)`
normalized by `vol(V(F) \ V(𝔸)) = 1`.

## Auxiliary results

All are in the namespace `Langlands.Global` (the last four in `Langlands.Global.AdelicGroupPoints`).

- `isLeftInvariantUnder_sup`: a function on `G(𝔸)` left invariant under two subgroups is left
  invariant under their join. The elements `x` with `f(xg) = f(g)` for all `g` form a subgroup.
- `map_rational_eq_rational`: the adelic-point map of a group-scheme homomorphism sends the
  principal image of a rational point to the principal image of its image
  (`rational_naturality`).
- `IsIwasawaCompact.intertwiningIntegral_radical_mul`: for `y ∈ V(𝔸)` (a point of
  `AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)`), `I λ (y g) = I λ g`. The
  rational quotient `V(F) \ V(𝔸)` is compact (`compactSpace_rationalQuotient_range_unipotent`), so
  Haar measure on `V(𝔸)` is right invariant (`haar_isMulRightInvariant_of_compactRationalQuotient`),
  and right translation by `y` on `Γ \ V(𝔸)` preserves the quotient measure
  (`LeftCosetSpace.measurePreserving_rightTranslate_discrete`). It is a homeomorphism, hence a
  measurable embedding. By `intertwiningIntegrand_mk` the integrand at `y g` and class `x` equals
  the integrand at `g` and the class `x y`; change variables.
- `IsIwasawaCompact.intertwiningIntegral_levi_rational_mul`: for a rational point `m₀` of `M'` with
  image `m'` in `G(𝔸)`, `I λ (m' g) = I λ g`. Let `α` be conjugation by `m'` on `V(𝔸)`
  (`EisensteinConstantTerm.conjAdelic`, using that `V` is normal in `Q`). It preserves `V(F)`
  (`conjAdelic_mem_rationalSubgroup_iff`), hence the normalized Haar measure
  (`EisensteinConstantTerm.measurePreserving_of_preserves`, applied to the Library's fundamental
  domain), and it preserves the adelic stabilizer `V(𝔸) ∩ wU(𝔸)w⁻¹`
  (`conjAdelic_mem_intertwiningAdelicStabilizer_iff`, from the Weyl conjugation), hence `Γ`
  (`intertwiningRationalSubgroup_eq_rational_inf_stabilizer`). The induced map on `Γ \ V(𝔸)`
  preserves the quotient measure (`LeftCosetSpace.measurePreserving_discreteQuotientMeasure`).
  At the class of `α(v)` the integrand at `m' g` is `φ_λ(w⁻¹ m' v g)`, and
  `w⁻¹ m' w = p(m_P)` for the rational point `m_P = (c ≫ l)(m₀)` of `P`
  (`IsWeylConjugation.adelic_comp_eq`, `map_rational_eq_rational`). So it equals
  `φ_λ(m_P · w⁻¹ v g) = φ_λ(w⁻¹ v g)` (`IsIwasawaCompact.parameterTwist_map_rational_mul`, from the
  left `U(𝔸)M(F)`-invariance of `φ`); change variables.
- `IsIwasawaCompact.continuous_intertwiningIntegral`: if, for every compact `C ⊆ G(𝔸)`, one
  integrable function on `Γ \ V(𝔸)` bounds the integrand for all `g ∈ C`, then `I λ` is
  continuous. At `g₀` take a compact neighbourhood (`G(𝔸)` is locally compact) and apply
  `continuousAt_of_dominated`. The integrand is continuous on the quotient
  (`continuous_intertwiningIntegrand`), hence a.e. strongly measurable, and continuous in `g` at
  each class.
- `IsMaximalCompactSubgroup.map_finite_le_comap_ofFinite`: for a maximal compact `K` of `G(𝔸)`,
  every point of the finite projection of `K`, placed in `G(𝔸)` with trivial infinite
  component, lies in `K`. This uses that `K` is the product of its two projections
  (`IsMaximalCompactSubgroup.eq_comap_prod`).

## The main proof (`intertwiningUniformAutomorphy_of_analytic`)

Fix the data. Five results give thresholds: `R₁` from `IntertwiningSmoothSlicesStatement`,
`R₂` and the ideal `J` from `IntertwiningUniformCenterIdealStatement`, `R₃` from
`intertwiningModerateGrowth` (module `AdelicIntertwiningModerateGrowthProof`), `R₄` from
`intertwiningAbsoluteConvergence` and `R₅` from `intertwiningIntegrability`. Take `R₀` their
maximum and the ideal `J`. Regularity at `R₀` implies regularity at each of them, since
`IsRegularParameter R λ` says `R < B(Re λ, α)` for every root `α` of `A` in the unipotent
radical of `P`. For an
`R₀`-regular `λ`:

1. **Left invariance under `V(𝔸)M'(F)`** (`parabolicQuotientSubgroup F q iV l'`, the join of the
   images of `V(𝔸)` and `M'(F)`), by `isLeftInvariantUnder_sup`.
   - For `v ∈ V(𝔸)`: `m_Q(vg) = m_Q(g)` (`heightPower_unipotent_mul`, `V` unipotent) and
     `I λ (vg) = I λ g` (`intertwiningIntegral_radical_mul`).
   - For `m' ∈ M'(F)`: `I λ (m'g) = I λ g` (`intertwiningIntegral_levi_rational_mul`) and
     `m_Q(m'g) = m_Q(g)` (`heightPower_rational_mul`, after writing `m'` as the image of a
     rational point of `Q`).
2. **Smoothness.** Continuity: `I λ` is continuous by `continuous_intertwiningIntegral`, the
   majorants coming from `intertwiningAbsoluteConvergence` with the compact parameter set
   `{λ}` in linear coordinates (`exists_complexParameterEquiv`), and `m_Q^{-wλ}` is continuous
   (`continuous_heightPower`). Plot-smooth slices: the premise `IntertwiningSmoothSlicesStatement`.
   Finite level: `φ` is fixed by an open subgroup `L` of `G(𝔸_f)`; the subgroup
   `L ⊓ (finite projection of K)` is open (`IsMaximalCompactSubgroup.isOpen_finite`), lies in
   `K` (`map_finite_le_comap_ofFinite`) and fixes `φ`, so it fixes `T λ`
   (`IsIwasawaCompact.intertwiningOperator_fixedByFiniteLevel`).
3. **Finiteness under the infinite part of `K`**:
   `IsIwasawaCompact.intertwiningOperator_isInfiniteSubgroupFinite`, with integrability of the
   integrand at every `g` from `intertwiningIntegrability`.
4. **`𝔷`-finiteness and the uniform clause**: the premise
   `IntertwiningUniformCenterIdealStatement` with its ideal `J`, used twice.
5. **Moderate growth**: `intertwiningModerateGrowth`.

## Provenance

The conclusion is Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
II.1.6, Proposition (i), printed pp. 87–88 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`06.1_pp_78_100_Definitions.pdf`, SHA-256
`948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`), with the ideal independent
of `λ` from the proof of the Lemma in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series* (2024), §8.2, p. 222 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal PDF SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`). The sources do not
spell out left invariance, continuity, the level and compact finiteness; the arguments above are
internal to the Library and use its quotient `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, whose comparison with
the quotient `(V(𝔸) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` is the Remark of Mœglin–Waldspurger II.1.6 (p. 87).

## Reduction using left invariance of the operator

`IntertwiningAutomorphyReductionStatement` derives uniform automorphy from the published propositions on plot-smooth infinite slices and a common finite-codimensional center ideal. `intertwiningUniformAutomorphy_of_smoothSlices_of_centerIdeal` proves the implication. It takes the maximum of the thresholds for the two hypotheses, absolute convergence, and the global polynomial growth bound proved in `AdelicIntertwiningModerateGrowthProof`.

Continuity follows by dominated convergence on each compact neighborhood in the adelic point group, using the majorant for the fixed parameter and pointwise continuity of the twisted inducing function. Left invariance comes from `AdelicIntertwiningLeftInvariance`. Convergence gives the domain needed to transfer compact finiteness. The intersection of the source finite level with the finite factor of the maximal compact is an open level fixing the output by compact equivariance. The same center ideal supplies both center finiteness of each output and the uniform assertion.

The automorphy conclusion is the one in Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*, II.1.6 (i), printed pp. 87–88. The uniform center condition is the one used in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §8.2, p. 222, in the proof of the Lemma on the span of regular intertwining values.
