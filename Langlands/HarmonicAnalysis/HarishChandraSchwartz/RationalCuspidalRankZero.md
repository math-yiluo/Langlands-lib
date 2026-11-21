# Waldspurger VIII.4 in relative rank zero, and the upper inclusion from its inputs

This module does two things for Waldspurger's Proposition VIII.4.1 and
Theorem VIII.4.2 on the Library's actual rational-point interfaces.

1. **General groups, conditionally.** It connects the published upper step
   `rationalCuspidalDiscreteUpperEstimate` to the Library's proved weight
   results. What remains open in the upper inclusion `p_χ(°C(G)) ⊆ A₂(G)_χ`
   is then only the structural special-compact data of Lemma II.1.5 and the
   finiteness of VIII.4.1. Together with the accepted lower inclusion of
   `RationalDiscreteCoefficientCuspLift`, the published equality
   `RationalCuspidalDiscreteCoefficientStatement` follows from three
   published, unproved propositions, taken as hypotheses:
   - `JointSpecialCompactBasisExistenceStatement`;
   - `RationalSchwartzConstantTermConvergenceStatement`;
   - `RationalCuspidalCentralProjectionFiniteStatement`.

   This is not a proof of the closed target.
2. **Groups without simple relative roots, unconditionally.** When
   `simpleRelativeRoots i ν = ∅`, the module proves VIII.4.1, the
   same-level lifting of VIII.5, and the equality of VIII.4.2, with no
   hypothesis beyond the binders of the published targets and
   `simpleRelativeRoots i ν = ∅`. These four rank-zero propositions are new
   derived statements, defined and proved here. Each one is the
   corresponding published proposition with the extra binder
   `simpleRelativeRoots i ν = ∅` placed right after `IsGenericCocharacter i ν`.

## Provenance

Page numbers are those of Waldspurger (2003); the PDF page is the printed
page minus 234.

- I.1, printed p.239 (PDF p.5): `A_G` is the largest split torus in the
  centre of `G`, and `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`. In the Library `A_G(F)` is the range
  `(rationalPoints.map s).range` of a split component `s`, and `G¹` is
  `rationalCommonNormKernel G`.
- VIII.4, printed p.327 (PDF p.93): `p_χ f(g) = ∫_{A_G} χ⁻¹(a) f(a g) da`
  (the Library's `centralProjection muA χ`), `°C_H = °C(G) ∩ C_H` (III.6),
  and Proposition VIII.4.1: "Pour tout sous-groupe ouvert compact `H` de `G`
  et tout `χ ∈ Â_G`, l'espace `p_χ(°C_H)` est de dimension finie."
- VIII.4, printed p.330 (PDF p.96): `E₂(G)_χ`, `A₂(G)_χ = ⊕_{ω ∈ E₂(G)_χ} A(ω)`
  and Theorem VIII.4.2: "Pour tout `χ ∈ Â_G`, on a l'égalité
  `p_χ(°C(G)) = A₂(G)_χ`." The proof of the inclusion `⊆`
  (printed pp.330–331) uses the right-translation representation on
  `p_χ(°C(H \ G))`, which is unitary and admissible by VIII.4.1. The
  published `rationalCuspidalDiscreteUpperEstimate` formalizes that step
  under local weight inputs and finite level spans.
- VIII.5, printed p.332 (PDF p.98): the `H × H`-invariant coefficients of
  the classes in `E₂(G)^H_χ` lie in `p_χ(°C_H)`. This is the published
  `RationalCuspidalFixedCoefficientLiftingStatement`.
- III.7, printed p.273 (PDF p.39): for an admissible square-integrable
  representation `ω`, a coefficient `f ∈ A(ω)`, and `ϕ ∈ C_c(G/G¹)`, the
  product `f ϕ` is in `C(G)` by Corollary III.1.2. The Library lemma
  `mul_mem_rationalSchwartz` takes rapid decay of the coefficients on `G¹`
  as an input. In the rank-zero proof below, compactness of `G¹` gives this
  decay for every smooth coefficient, without a square-integrability premise.
- Lemma II.1.5, printed p.252 (PDF p.18): the `L²` weight estimate for `Ξ`.
  The Library statement `RationalXiSquareIntegrableStatement` uses a compact
  open `K0` with the simultaneous standard basis and finite Cartan covering,
  a compact open Iwasawa realization, a closed matrix realization and a Haar
  measure on `G(F)`. The upper bound of Lemma II.1.1 (printed p.251 / PDF p.17)
  is a premise of the proof `rationalXiSquareIntegrable_of_upperBound`, not
  of the statement. Here that premise is discharged by `rationalXiUpperBound`.

Waldspurger does not single out groups without simple relative roots. The
rank-zero results and their route are derived, not in the source: `Ξ = 1`,
`G¹` is compact, every Schwartz function is cuspidal, and `G(F) = A_G(F) X H`
for a finite set `X`.

## Finite dimensionality from a finite double-coset cover

Section `Finite`. `Γ` is a group.

- `centralRightInvariantSubmodule A H χ` (definition): for subgroups `A` and
  `H` of `Γ` and a homomorphism `χ : A →* ℂˣ`, the submodule of functions
  `f : Γ → ℂ` with `f(a g) = χ(a) f(g)` for all `a ∈ A`, `g ∈ Γ` and
  `f(g h) = f(g)` for all `h ∈ H`, `g ∈ Γ`.
- `finiteDimensional_centralRightInvariantSubmodule`: if `X` is a finite set
  with every `g ∈ Γ` of the form `a x h` (`a ∈ A`, `x ∈ X`, `h ∈ H`), then
  this submodule is finite dimensional. Restriction to `X` is injective on
  it.
- `exists_finset_eq_mul_mul`: let `Γ` be a topological group, `N` a compact
  normal subgroup, `A` a subgroup of the centre with `Γ ⧸ (N ⊔ A)` finite,
  and `H` an open subgroup. Then `Γ = A X H` for a finite set `X`. The
  compact set `N` is covered by finitely many sets `z⁻¹ H` (`z ∈ t`).
  Writing `g = y n b`, with `y` the chosen representative of the class of
  `g` in `Γ ⧸ (N ⊔ A)`, `n ∈ N` and `b ∈ A`, one gets
  `g = b (y z⁻¹)(z n)` with `z n ∈ H`, by centrality of `b`. So
  `X = {y z⁻¹}` works.

## Rapid decay on a compact subgroup

Section `Compact`. `Γ` is a group with a topology.

- `isRapidlyDecreasingOn_of_isCompact`: for continuous `Ξ > 0`, continuous
  `σ ≥ 0` and a compact subgroup `N`, every continuous `f : Γ → ℂ` is
  rapidly decreasing on `N`: for each `r` there is `c` with
  `‖f n‖ ≤ c Ξ(n) (1 + σ(n))^{-r}` on `N`. The continuous function
  `‖f‖ / (Ξ (1 + σ)^{-r})` is bounded on the compact set `N`.
- `hasRapidlyDecreasingCoefficientsOn_of_isCompact`: if moreover `Γ` is a
  topological group, all coefficients `g ↦ ℓ(A(g) v)` of every smooth
  representation `A` are rapidly decreasing on `N`, since they are
  continuous (`coefficientTensorMap`).

## Rational points

Section `Rational`. `F` is a nonarchimedean local field and `G` is
connected reductive (`hG`), with a maximal split torus `i` (`hi`) and a
generic cocharacter `ν` (`hν`). `K` is a compact open subgroup with
`G(F) = P₀(F) K` (`hPK`) and `ρ` is a matrix representation; they fix the
Schwartz space `RationalSchwartzSpace hKc hPK ρ`. `s` is a split component
(`hs`) and `muA` is a Haar measure on `A_G(F)`.

### The upper inclusion from its weight inputs

- `rationalCuspidalCentralImage_subset_of_specialCompact`. Hypotheses: a
  compact open subgroup `K0` with `SimultaneousStandardBasisAt i ν K0` and
  `FiniteCartanCovering F i ν K0` (the structural premises of the Library's
  Lemma II.1.5), and `ρ` closed. Conclusion: for every Haar measure `mu` on
  the Borel quotient `G(F) ⧸ A_G(F)` and every continuous unitary character
  `χ`, if every level span `rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ J`
  at a compact open `J` is finite dimensional, then
  `rationalCuspidalCentralImage hKc hPK ρ muA χ` lies in
  `discreteSeriesCentralCoefficientSpace.{u, max u uV} A_G(F) _ mu χ`.

  The proof applies `rationalCuspidalDiscreteUpperEstimate` with a Haar
  measure on `G(F)`. The central weights come from
  `RationalSplitCenterHeightStatement.centralWeights` and the proved
  `rationalSplitCenterHeight`. The `L²` weights come from
  `RationalXiSquareIntegrableStatement.l2Weights`, applied to
  `rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound` (Lemma
  II.1.5 from the proved upper bound of Lemma II.1.1) and to the data of
  `K0`.

### Relative rank zero

All four lemmas assume `simpleRelativeRoots i ν = ∅` (`h0`).

- `rankZero_isCentral_unipotent_eq_bot`: `i` is central (`IsCentral i`) and
  the radical `standardUnipotentPoints i ν ∅` of the minimal standard
  parabolic subgroup is trivial. By the published
  `standardParabolicEndpoints`, the Levi subgroup and radical attached to the
  empty set are the torus centralizer and the minimal radical. Those attached
  to the full set of simple roots are `⊤` and `⊥`. When the set of simple
  roots is empty the two ends coincide. So `torusCentralizer i = ⊤`, which
  is centrality by `isCentral_iff_torusCentralizer_eq_top`.
- `rationalXi_eq_one_of_simpleRoots_empty`: `rationalXi hKc hPK g = 1` for
  every `g`. The modulus `rationalMinimalModulus i ν` of `P₀(F)` is trivial
  because the radical is (`closedNormalizerCharacter_eq_one_of_commute`).
  Then the definitions `rationalXi`, `xi` and `iwasawaWeight` reduce to `1`.
- `isCompact_rationalCommonNormKernel_of_simpleRoots_empty`: `G¹` is
  compact, by `isCompact_rationalCommonNormKernel_of_central_maximalSplit`
  for the central maximal split torus `i`.
- `finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty`:
  for every open subgroup `H` (compactness is not needed) and every
  homomorphism `χ : A_G(F) →* ℂˣ`, the level span
  `rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H` is finite dimensional.
  This is the finiteness half of VIII.4.1. The quotient
  `G(F) ⧸ (G¹ ⊔ A_G(F))` is finite (`finite_rationalCentralQuotient` and
  `finiteIndex_splitValuationImage_of_isSplitComponent`) and `G¹` is
  compact. So `G(F) = A_G(F) X H` for a finite `X` by
  `exists_finset_eq_mul_mul`. Each `p_χ(φ)`, with `φ` in the level, lies in
  `centralRightInvariantSubmodule A_G(F) H χ` (`centralProjection_mul_left`
  and `IsBiInvariant.centralProjection`; `muA` is right invariant because
  `A_G(F)` is central). That submodule is finite dimensional by
  `finiteDimensional_centralRightInvariantSubmodule`.
- `exists_cuspidal_lift_of_simpleRoots_empty`: the direct cusp lift without
  square integrability. Let `χ : A_G(F) →* ℂˣ` and let `A` be a smooth
  representation `SmoothRep.{0, u, uV} ℂ (rationalPoints G)` on which every
  `a ∈ A_G(F)` acts by the scalar `χ(a)`. Then every
  `f ∈ coefficientFunctionSpace A` has a Schwartz function `φ` such that:
  - `φ ∈ rationalCuspidalSubmodule hKc hPK ρ`;
  - `centralProjection muA χ φ = f`;
  - for every compact subgroup `H`, if `f` is `H`-bi-invariant then so is `φ`.

  As in `DiscreteCoefficientCuspLift.exists_cuspidal_lift`, `φ = m⁻¹ f c`,
  with `c = transversalCutoff G¹ A_G(F)` and `m = μ_A(A_G(F) ∩ G¹)`, which is
  positive (`centralNormKernelMass_pos`). The coefficients of `A` are rapidly
  decreasing on the compact `G¹` (`hasRapidlyDecreasingCoefficientsOn_of_isCompact`
  with `Ξ = rationalXi`, `σ = rationalHeight ρ`). So `f c` is Schwartz by
  `mul_mem_rationalSchwartz`. It is cuspidal because
  `rationalCuspidalSubmodule hKc hPK ρ = ⊤`
  (`rationalCuspidalSubmodule_eq_top_of_simpleRoots_empty`). The projection
  is `centralProjection_smul_mul_transversalCutoff`. Bi-invariance follows
  from `isBiInvariant_mul_quotient`, since compact subgroups lie in `G¹`
  (`compactSubgroup_le_rationalCommonNormKernel`).

## Statements and assembly

- `RationalCuspidalDiscreteCoefficientUpperInclusionStatement`
  (proposition): the binders of `RationalCuspidalDiscreteCoefficientStatement`
  with the conclusion
  `rationalCuspidalCentralImage hKc hPK ρ muA χ ⊆ discreteSeriesCentralCoefficientSpace.{u, max u uV} ...`.
  It is the inclusion `⊆` of Theorem VIII.4.2, with the published carrier
  convention `max u uV`.
- `rationalCuspidalDiscreteCoefficientUpperInclusion_of_joint`: from
  `JointSpecialCompactBasisExistenceStatement.{u}` and
  `RationalCuspidalCentralProjectionFiniteStatement.{u}`, it derives
  `RationalCuspidalDiscreteCoefficientUpperInclusionStatement.{u, uV}`. The
  data `K0` come from `exists_constantTermPremises_of_joint`. The finite
  level spans come from the second conjunct of VIII.4.1.
- `rationalCuspidalDiscreteCoefficient_of_inclusions`: the upper inclusion
  at `.{u, uV}` and the published
  `RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, max u uV}`
  give `RationalCuspidalDiscreteCoefficientStatement.{u, uV}`, by
  antisymmetry.
- `rationalCuspidalDiscreteCoefficient_of_joint`: from
  `JointSpecialCompactBasisExistenceStatement.{u}`,
  `RationalSchwartzConstantTermConvergenceStatement.{u}` and
  `RationalCuspidalCentralProjectionFiniteStatement.{u}`, it derives
  `RationalCuspidalDiscreteCoefficientStatement.{u, uV}`. The lower
  inclusion is
  `DiscreteCoefficientCuspLift.rationalCuspidalDiscreteCoefficientLowerInclusion_of_joint`.
  This is conditional: the three hypotheses are open.

The rank-zero propositions, each with its proof:

- `RationalCuspidalCentralProjectionFiniteRankZeroStatement`, proved by
  `rationalCuspidalCentralProjectionFiniteRankZero`: Proposition VIII.4.1
  in rank zero. For every compact open `H`, the carrier of the level span
  equals the raw level image `rationalCuspidalCentralLevelImage`, and the
  span is finite dimensional. The first conjunct follows from central
  convergence on the whole Schwartz space (the published
  `rationalSchwartzCentralConvergence`) and
  `coe_schwartzCentralIntegralSpan_eq_image`.
- `RationalCuspidalFixedCoefficientLiftingRankZeroStatement`, proved by
  `rationalCuspidalFixedCoefficientLiftingRankZero`: the level-preserving
  lifting of VIII.5 in rank zero, with independent `uV`. For a class `ω` in
  `discreteSeriesCentralFixed`, `A_G(F)` acts on the representative
  `ω.val.out.obj` by `χ`. The lift of
  `exists_cuspidal_lift_of_simpleRoots_empty` is cuspidal and
  `H`-bi-invariant, so it lies in `rationalCuspidalLevel hKc hPK ρ H`.
- `RationalCuspidalDiscreteCoefficientLowerInclusionRankZeroStatement`,
  proved by `rationalCuspidalDiscreteCoefficientLowerInclusionRankZero`: the
  inclusion `A₂(G)_χ ⊆ p_χ(°C(G))` in rank zero, for the coefficient space
  `discreteSeriesCentralCoefficientSpace.{u, uV}`. The lifts of
  `exists_cuspidal_lift_of_simpleRoots_empty` put every coefficient space
  of a class in `E₂(G)_χ` into the span of the image
  (`discreteSeriesCentralCoefficientSpace_le_iff`). By central convergence
  that span is the raw image.
- `RationalCuspidalDiscreteCoefficientRankZeroStatement`, proved by
  `rationalCuspidalDiscreteCoefficientRankZero`: Theorem VIII.4.2 in rank
  zero, `rationalCuspidalCentralImage hKc hPK ρ muA χ =
  discreteSeriesCentralCoefficientSpace.{u, max u uV} ...`. The inclusion
  `⊇` is the rank-zero lower inclusion at `.{u, max u uV}`. The inclusion
  `⊆` is `rationalCuspidalDiscreteUpperEstimate` with:
  - the central weights as above;
  - the `L²` weights from `rationalL2Weights` and
    `rationalSquareIntegrableWeight_of_compact_normKernel`, using `Ξ = 1`
    and the compactness of `G¹`;
  - the finite level spans of
    `finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty`.

  No special-compact data are needed in rank zero.
