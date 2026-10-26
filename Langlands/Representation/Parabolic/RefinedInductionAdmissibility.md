# Admissibility of actual normalized refined induction

Author: Worker 717.

This module proves that actual normalized induction from a refined parabolic
of a product Levi preserves admissibility. Its closing theorem
`Langlands.Parabolic.refinedCuspidalInduction_isAdmissible` is exactly the
first conjunct, `IsAdmissible I.ρ`, of the published proposition
`Langlands.CuspidalSupport.RefinedCuspidalInductionFiniteLengthStatement` in
[`RefinedCuspidalInductionLengthStatement`](../CuspidalSupport/RefinedCuspidalInductionLengthStatement.md).
The module does not prove the finite-length or composition-series conjuncts
of that proposition, and it does not prove the proposition itself.

Throughout, `p` is an arbitrary prime, `F : PadicField.{uF} p`,
`T : F.TopologicalData` is a compatible topological realization, `n` is any
natural rank, `B : GeneralLinear.BlockShape n` and
`S : Geometric.BlockRefinement B`. Every block shape, every refinement
(including equality refinements and empty outer products) and rank zero are
included. The field universe `uF` and the representation universe `uV` are
independent. The topologies are `T.topology` and `T.leviTopologicalGroup B`,
the ones used by `T.normalizedRefinedInduced`.

## Declarations

- `Langlands.isOpenMap_of_continuous_rightInverse`: for groups `H` and `G`
  with topologies, `ContinuousMul H`, a homomorphism `q : H →* G` and a
  continuous function `s : G → H` with `q (s g) = g` for all `g`, the map `q` is
  open. The right inverse `s` need not be a homomorphism, and no topological
  group structure on `G` is required.
- `Langlands.Parabolic.isOpenMap_refinedLeviProjection T B S`: the actual
  projection `refinedLeviProjection F.Carrier B S` from the refined parabolic
  `refinedParabolic F.Carrier B S` onto the refined Levi
  `refinedLevi F.Carrier B S` is an open map.
- `Langlands.Parabolic.isAdmissible_refinedInflation_iff T B S σ`: for any
  complex representation `σ` of `refinedLevi F.Carrier B S` on any
  `V : Type uV`, `σ.comp (refinedLeviProjection F.Carrier B S)` is admissible
  if and only if `σ` is admissible.
- `Langlands.Parabolic.refinedQuotientMap_image_integralRange T B S`: the
  image of the product over the outer blocks `i` of the integral groups
  `Iwasawa.integralRange v (B.size i)` (that is, `GL_{B.size i}(O)`, where
  `v = ValuativeRel.valuation F.Carrier`) under the quotient map
  `Induction.quotientMap (refinedParabolic F.Carrier B S)` is the whole
  quotient.
- `Langlands.Parabolic.refinedParabolicQuotientCompact F T B S`: the actual
  coset space `Induction.LeftQuotient (refinedParabolic F.Carrier B S)` is a
  compact space for the quotient topology of `T.topology`. Its points are the
  right cosets `P g` with `P` the refined parabolic.
- `Langlands.Parabolic.normalizedRefinedInductionAdmissibility F T B S σ`: if
  `σ` is admissible, then `T.normalizedRefinedInduced B S σ` is admissible.
  There is no irreducibility, finite-dimensionality or cuspidality assumption
  on `σ`.
- `Langlands.Parabolic.RefinedInductionAdmissibilityClause F T B S V` is the
  record's named definition, a proposition (`Prop`) packaging the previous
  item for a fixed carrier: under `T.topology` and `T.leviTopologicalGroup B`,
  for every `σ : Representation ℂ (refinedLevi F.Carrier B S) V`,
  `IsAdmissible σ → IsAdmissible (T.normalizedRefinedInduced B S σ)`. It is the
  refined analogue of the published `NormalizedInductionAdmissibilityClause`
  from [`NormalizedInductionStatement`](NormalizedInductionStatement.md), with
  the refined parabolic, its projection and its positive half-modulus in place
  of the standard block parabolic of `GL_n`.
- `Langlands.Parabolic.refinedInductionAdmissibilityClause_holds F T B S V`
  proves this clause for every `F`, `T`, `B`, `S` and `V`.
- `Langlands.Parabolic.isAdmissible_flattenedLeviTransport_iff F T B S ρ`: for
  any complex representation `ρ` of the flattened Levi
  `(B.flatten S).Levi F.Carrier`, the pullback
  `ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom` to the refined
  Levi is admissible if and only if `ρ` is.
- `Langlands.Parabolic.refinedCuspidalInduction_isAdmissible F T B S ω`: for
  `ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)` with
  `CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ`,
  `(Rep.of (T.normalizedRefinedInduced B S σ)).ρ` is admissible, where
  `σ = ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`. This is
  the induced object `I` of the target statement, with the same transport, the
  same carrier and the same `Rep.of` packaging. Irreducibility of `ω` is not
  needed for this conjunct, so it is not a hypothesis.

## Implemented proof

1. `isOpenMap_of_continuous_rightInverse`. Let `U` be open and `u ∈ U`. The
   function `f g = u * (s (q u))⁻¹ * s g` is continuous, satisfies
   `f (q u) = u`, and `q (f g) = g` because `q` is a homomorphism and `s` is a
   right inverse. So `f⁻¹' U` is a neighbourhood of `q u` contained in `q '' U`.
2. `isOpenMap_refinedLeviProjection` applies step 1 with the published section
   `refinedLeviSection F.Carrier B S`, its continuity
   `refinedLeviSectionContinuous` and
   `refinedLeviProjection_section`, under `T.topology`, `T.valuativeRel`,
   `T.localField` and `T.leviTopologicalGroup B`.
3. `isAdmissible_refinedInflation_iff` is the published generic
   `isAdmissible_comp_iff_of_open_surjective` from
   [`LeviInflationAdmissibilityProof`](LeviInflationAdmissibilityProof.md),
   applied to the projection with its continuity
   `refinedLeviProjectionContinuous`, openness from step 2, and surjectivity
   from the section.
4. `refinedQuotientMap_image_integralRange`. Given a quotient point with
   representative `g` in the product Levi, the published
   `Iwasawa.exists_mul_upperTriangular v (B.size i) (g i)` chooses, for every
   outer block `i`, an integral `k i` with `g i * k i` upper triangular. The
   published `BlockShape.mem_parabolic_of_isUpperTriangular` for the inner
   shape `S i` puts `g i * k i` in `(S i).parabolic F.Carrier`, so by
   `mem_refinedParabolic` the product `g * k` lies in the refined parabolic.
   Hence the integral element `k⁻¹` (inverse closure of each integral group)
   is related to `g` by `QuotientGroup.rightRel`, and its class is the class
   of `g`.
5. `refinedParabolicQuotientCompact`. Each integral group is compact by the
   published `Parabolic.isCompact_integralRange T (B.size i)` from
   [`QuotientCompactProof`](QuotientCompactProof.md), which includes rank
   zero. Mathlib's `isCompact_univ_pi` makes the product compact; its image
   under the continuous quotient map is the whole space by step 4.
6. `normalizedRefinedInductionAdmissibility`. The admissible `σ` inflates to
   an admissible representation of the refined parabolic by step 3. The
   published `isAdmissible_twist_iff` from
   [`Twist/AdmissibilityProof`](../Twist/AdmissibilityProof.md), with the
   published open-kernel fact `T.isOpen_ker_refinedParabolicHalfModulus B S`,
   preserves admissibility under the positive half-modulus twist. With
   compactness from step 5, the published
   `Induction.smoothInduced_isAdmissible_of_compactSpace` from
   [`Induction/CompactQuotientProof`](../Induction/CompactQuotientProof.md)
   gives admissibility of the smooth induction of the twisted inflation. This
   is the action `T.normalizedRefinedInduced B S σ` by its definition in
   `Geometric/RefinementFunctors`. `refinedInductionAdmissibilityClause_holds`
   is this theorem with `σ` universally quantified.
7. `isAdmissible_flattenedLeviTransport_iff` applies
   `isAdmissible_comp_iff_of_open_surjective` to the inverse of the published
   topological group isomorphism `flattenedLeviEquivContinuous F.Carrier B S`
   from `Geometric/FlattenedLevi`, which is continuous, open and surjective.
8. `refinedCuspidalInduction_isAdmissible` takes the admissibility component
   of `IsLeviCuspidal`, transports it by step 7 and applies step 6.

No quotient-compactness, openness, Iwasawa factorization, positive-rank or
finite-cover assumption is added; all such facts are proved or imported.

## Provenance

The provenance is internal. The module is the refined-parabolic analogue of
the published `Parabolic.normalizedInductionAdmissibility` (see
[`NormalizedAdmissibilityProof`](NormalizedAdmissibilityProof.md) for its
original-source correspondence: compactness of `P \ G` and admissibility of
normalized parabolic induction in Casselman's notes and in Bernstein and
Zelevinsky). Here the ambient group is the product Levi `B.Levi F.Carrier`, a
product of general linear groups, and the parabolic is the product of the
inner block parabolics of `S`. Compactness is proved blockwise from the same
Iwasawa decomposition. The module serves the admissibility conjunct of the
refined cuspidal induction target of task
`41b7dd0e-c19d-48ad-944c-f1ab3cf3e96b`.
