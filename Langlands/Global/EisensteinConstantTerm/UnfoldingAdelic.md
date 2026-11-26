# Adelic forms of the unfolding ingredients

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingAdelic`, namespace `Langlands.Global`.
It connects the Library's adelic measures and subgroups with the abstract conventions of
`UnfoldingAbstract`, and defines the subgroup predicate `UnfoldingSubgroupStructure`.

## Discrete quotients

For a discrete `Γ` in a second countable group `X` and a measure `μ`, and a left `Γ`-invariant
measurable `g`: `integral_discreteQuotientMeasure_out`, `lintegral_discreteQuotientMeasure_out`
and `integrable_discreteQuotientMeasure_out_iff` express integrals of `q ↦ g(Quotient.out q)`
against `LeftCosetSpace.discreteQuotientMeasure Γ hΓ μ` as integrals of `g` over the chosen
fundamental domain (`out_mk_eq_mul`, `measurable_comp_out`). `fundamentalDomain_congr` and
`normalizedHaar_congr` transport along equal subgroups.

## Adelic subgroups

- `rationalSubgroup_le_latticeOf`, `rationalSubgroup_range_eq_latticeOf`: the principal image
  `AdelicSubgroupPoints.rationalSubgroup F G W` lies in the intersection of the adelic points with
  `G(F)`, with equality for the range of a closed subgroup (by the Library's
  `rational_mem_adelicPoints_range_iff`).
- `normalizedHaarMeasure_eq_normalizedHaar`: for a closed subgroup `j`, the Library's
  `normalizedHaarMeasure F G (range j)` is `normalizedHaar` of the lattice
  `G(F) ∩ (range j)(𝔸)`.
- `subgroupConstantTerm_eq_setIntegral`: the Library's `subgroupConstantTerm F j φ x` is the
  average of `u ↦ φ(u x)` over the chosen fundamental domain of that lattice, for `φ` measurable
  and left invariant under the rational image of `j`.
- `exists_cover_latticeOf_range` (smooth connected unipotent `H`, from the Library's
  `exists_isCompact_rational_mul_mem_range`) and `exists_cover_conjStab` (the stabilizer
  `V(𝔸) ∩ w U(𝔸) w⁻¹`, from the Library's `intertwiningStabilizer`): compact sets meeting every
  orbit of the rational lattices.

## `UnfoldingSubgroupStructure`

`UnfoldingSubgroupStructure F p iU q iV w f iU' g' iV'` is the conjunction of three subgroup
facts in `G(𝔸)`, where `V`, `V'`, `U`, `U'` denote the adelic points of the radicals
`iV ≫ q`, `iV' ≫ g' ≫ q`, `iU ≫ p`, `iU' ≫ f ≫ p` and `w` the point `innerAdelicPoint F G w`:

1. if `v ∈ V` is rational and `w⁻¹ v w ∈ P(F)`, then `w⁻¹ v w ∈ U'`;
2. there is a closed subgroup `A ≤ U'` with `w A w⁻¹ ⊆ V`, such that `U ≤ U'` is normal,
   `A ∩ U = 1`, `U' = U A`, and the `A`-component of a rational point of `U'` is rational;
3. there is a closed subgroup `B ≤ V'` with `w⁻¹ B w ⊆ U`, such that `V ≤ V'` is normal,
   `B ∩ V = 1`, `V' = V B`, and the `B`-component of a rational point of `V'` is rational.

In the setting of Bernstein–Lapid Lemma 6.7 (journal p. 207), with `P' = P_w`, `Q' = Q_w` for a
standard representative `w ∈ QWP`: item 1 is the rational-point form of the identity
`U_Q ∩ w P w⁻¹ = U_Q ∩ w U_{P_w} w⁻¹` of Lemma 6.7 (3); item 3 is the adelic form of the
decomposition `U_{Q_w} = (M_Q ∩ w U_P w⁻¹) ⋉ U_Q` of Lemma 6.7 (3), with
`B = (M_Q ∩ w U_P w⁻¹)(𝔸)`; and item 2 is the same decomposition with the roles of `(P, w)` and
`(Q, w⁻¹)` exchanged, `U_{P_w} = (M_P ∩ w⁻¹ U_Q w) ⋉ U_P`, with `A = (M_P ∩ w⁻¹ U_Q w)(𝔸)`. The
predicate only asserts that some such `A` and `B` exist. These facts are used in the proof of
Bernstein–Lapid Lemma 6.10. Mœglin–Waldspurger II.1.7 (6) (printed p. 93),
`U'(k) ∩ w P(k) w⁻¹ = U'(k) ∩ w U(k) w⁻¹`, is the special case of item 1 for standard parabolics
with `w ∈ W(M, M')`, where `P_w = P`; their `P' = M' U'` plays the role of `Q` here.
