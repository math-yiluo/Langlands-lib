# Injectivity of leading cuspidal components, as a reduction

Module `Langlands.Global.AdelicLeadingCuspidalInjectivityReduction`.

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), Theorem 6.3
(§6.3, p. 203) with its proof in §6.5 (pp. 204–205), the lemma and corollary of §6.4
(pp. 203–204), Proposition 6.2 (p. 202; Mœglin–Waldspurger I.3.4) and Lemma 6.1 (p. 200).

## The statement

`LeadingCuspidalInjectivityReductionStatement.{u}` is the implication

`ParabolicCuspidalVanishingStatement.{u} → CuspidalExponentAscentStatement.{u} →
LeadingCuspidalInjectivityStatement.{u}`.

- `ParabolicCuspidalVanishingStatement` (module `AdelicCuspidalAnnihilator`) is the vanishing
  criterion (8.1) of BL in its fibrewise form: a continuous function of moderate growth on
  `U_P(𝔸) M_P(F) \ G(𝔸)` whose constant terms along all standard `Q ≤ P` have vanishing
  norm-one Levi pairings against all Levi cusp forms is zero. For `P = G` and automorphic input it
  gives Proposition 6.2 of BL (MW I.3.4). It assumes a closed embedding `rho` of positive size and Iwasawa coverage for
  every standard parabolic.
- `CuspidalExponentAscentStatement` (module `AdelicCuspidalExponentAscentStatement`) is the
  corollary of BL §6.4 for any chosen family of cuspidal projections and exponent decompositions.
- `LeadingCuspidalInjectivityStatement` (module `AdelicLeadingCuspidalInjectivityStatement`) is
  Theorem 6.3: two automorphic functions on `G(F) \ G(𝔸)` with a common family of leading cuspidal
  components agree.

`leadingCuspidalInjectivityReduction` proves the implication. The module proves no analytic
statement about automorphic forms; the two premises carry the analytic content.

## The proof

The supporting theorems are in the namespace `Langlands.Global.StandardParabolicFamily`.

### Roots

- `realExponent_mem_corootAnnihilator`: the image `Re λ ∈ 𝔞_0^*` of the real part of a
  parameter of `P_J` lies in the coroot annihilator of `J`. It is the restriction to `T` of a real
  character of `M_J`, and the published `standardLeviCharacterAnnihilator` identifies these
  restrictions with the coroot annihilator. `pair_realExponent_coroot_eq_zero` is the pointwise
  form `⟨Re λ, b^∨⟩ = 0` for `b ∈ J`.
- `pair_generic_neg_of_antidominant`: let `z` lie in the real span of a set `R` of simple roots,
  with `⟨z, b^∨⟩ ≤ 0` for all `b ∈ R` and `⟨z, α^∨⟩ < 0` for one `α`. Then `⟨z, ν⟩ < 0` for the
  generic cocharacter `ν` defining the minimal parabolic. The proof writes `z = p - n` with `p`
  and `n` nonnegative combinations of disjoint sets of roots of `R`, and uses the Weyl-invariant
  inner product `relativeWeylInvariantForm`. The coroot formula
  (`RelativeRootReflectionData.coroot_mul_form`) gives `B(z, b) ≤ 0` for `b ∈ R`, and distinct
  simple roots are obtuse (`RelativeRootReflectionData.simple_form_nonpos`). Hence
  `B(p, p) = B(z, p) + B(n, p) ≤ 0`, so `p = 0` and `z = -n`. Since `z ≠ 0`, the combination `n`
  has a positive coefficient, and every simple root pairs positively with `ν`.

### Linearity

- `constantTerm_sub_of_integrable`: the constant term is additive when both integrands are
  integrable. For continuous functions invariant under `G(F)` integrability is
  `hasIntegrableConstantTerm_of_rational`. It uses the published
  `integrable_constantTermIntegrand_of_le` for the full standard index and
  `parabolicQuotientSubgroup_top`.
- `IsCuspidalProjection.sub`: cuspidal projections of two inputs give a cuspidal projection of the
  difference. Automorphy uses the submodule `automorphicFunctionsOn`, cuspidality uses the
  published `isCuspidalAlong_sub`, and the pairing condition follows from the linearity of the
  integrand (`leviPairingIntegrand_sub`) and of the integral.
- `padComponents t c` extends a family of components by zero outside `t`.
  `IsExponentDecomposition.sub` combines decompositions `(s, c)` and `(s', c')` of two functions
  into a decomposition of the difference, indexed by `s ∪ s'`. The published
  `hasUnnormalizedExponent_sub` and `hasUnnormalizedExponent_zero` give the exponent clause.
  `leadingSum_padComponents` and `leadingSum_sub` compute the leading sum of the result.
- `exists_difference_family`: if `φ` and `ψ` have the same leading cuspidal components, then
  `φ - ψ` has a family of cuspidal projections and exponent decompositions
  (`IsCuspidalExponentFamily`) all of whose leading sums vanish.

### The argument of §6.5

`components_eq_zero_of_leadingSum_eq_zero`: for an automorphic `φ` and a family
`(φc, s, c)` with vanishing leading sums, every component `c Q λ`, `λ ∈ s Q`, vanishes. Suppose
not. The labels of nonzero components form a finite set (`finite_standardIndex`). Take the
smallest rank `r_0 = J.ncard` among them, and among the labels of rank `r_0` one `(P, λ)`
maximizing `⟨Re λ, ν⟩`. The leading sum along `P` is zero, so by the directness of (6.10)
(`eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent`) `λ` is not leading. Some simple root
`α` has `⟨Re λ, α^∨⟩ < 0`, and `α ∉ P` by the root lemma above. The premise
`CuspidalExponentAscentStatement` yields `(Q, μ)` with `Q ∪ {β} = P ∪ {α}`, `β ∉ Q`, `c Q μ ≠ 0`,
`⟨Re μ, β^∨⟩ ≥ 0` and `Re λ - Re μ` in the span of `P ∪ {α}`. Then `Q` has rank `r_0`. For
`b ∈ P ∪ {α}` one has `⟨Re λ, b^∨⟩ ≤ 0` (it is `0` on `P` and negative at `α`) and
`⟨Re μ, b^∨⟩ ≥ 0` (it is `0` on `Q` and nonnegative at `β`), so the antidominance lemma gives
`⟨Re λ, ν⟩ < ⟨Re μ, ν⟩`, contradicting the maximality.

BL use a vector `ϖ^∨` positive on the simple roots, the decompositions
`𝔞_P = 𝔞_P^{P_α} ⊕ 𝔞_{P_α}` and Lemma 6.1 (p. 200; the projections of `ϖ^∨` to `𝔞_P^{P_α}` and
`𝔞_Q^{P_α}` are positive multiples of the coroots). Here `ϖ^∨` is the generic cocharacter, and the
comparison is made inside `(𝔞_0^{P_α})^*` by the antidominance lemma.

### Conclusion for closed embeddings of positive size

`eq_of_leadingCuspidalComponents_of_pos`: all components of the family of `φ - ψ` vanish, so each
cuspidal projection is `0`. Hence the constant terms of `φ - ψ` lie in the cuspidal annihilators
(`InCuspidalAnnihilator`). `isIwasawaCompact_of_minimal` transfers the Iwasawa decomposition from
`P_∅` to every standard parabolic. The premise `ParabolicCuspidalVanishingStatement` for the
full standard index then gives `φ - ψ = 0`.

### The rank-zero case

A closed embedding into `GL_0` occurs only for the trivial group, and the vanishing criterion
assumes positive size. `subsingleton_hom_groupScheme_fin_zero` shows that `GL_0` has one point
over every base. Its structure morphism is an isomorphism (`isIso_SpecMap_iff`), because the
coordinate ring of `GL_0` is the base field. Hence `subsingleton_hom_of_rank_zero` holds for every
closed subgroup of `GL_0`. `isLeviCuspForm_one_of_rank_zero` shows that the constant function `1`
is a Levi cusp form for the full standard index. Its smoothness is `isPlotSmooth_const`, its
`K`-finiteness follows from the finite dimension of the functions on the one-point group, and its
center finiteness is `isCenterFiniteFunction_of_finiteDimensional`, which uses the orbit map of
the center and `LinearMap.quotKerEquivRange`. It is cuspidal because every subgroup of the
trivial group is the whole group. `eq_of_leadingCuspidalComponents_of_rank_zero` pairs the
constant term `C_G(φ - ψ) = φ - ψ` (`constantTerm_top`) with this cusp form. The pairing integrand
is the constant `(φ - ψ)(g)`, its integral vanishes because the cuspidal projection is `0`, and
the quotient Haar measure is nonzero (`normOneRationalQuotientHaarMeasure_ne_zero`). Integrability
of a nonzero constant forces a finite measure (`integrable_const_iff`), so `(φ - ψ)(g) = 0`.
This case uses `CuspidalExponentAscentStatement` but not the vanishing criterion.

## Scope

The reduction proves Theorem 6.3 for the Library's predicates exactly as stated in
`LeadingCuspidalInjectivityStatement`, including closed embeddings of size zero. It does not
prove either premise. It does not use the existence or uniqueness of cuspidal projections, since
it works with the projections and decompositions supplied by the hypotheses of Theorem 6.3.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234: §6.1 (roots, coroots and the decompositions of `𝔞_0`), §6.2
  (Proposition 6.2, p. 202), §6.3 (Theorem 6.3, p. 203), §6.4 (pp. 203–204), §6.5
  (pp. 204–205), (8.1) (p. 221).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995): I.3.4.
