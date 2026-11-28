# Specialization on the strict charts

On the strict chart `X^nr`, let `M = traitNearbyModel ι f`. The nearby-cycles
functor of this model is `Li* Rj_* Lε*`. Its source and total space are both
`X^nr`, with `ε = j ≫ id`. For a complex `K` on `X^nr`,
`chartSpecialization` feeds `NearbyCyclesModel.twistSpecializationMap` the
comparison `Lε*K ≅ Lj*K` obtained by composition and identity for derived
pullback. The result is `Li*K → Ψ_M(K)`. It applies `Li*` to the unit of
`Lj* ⊣ Rj_*` followed by the direct image of the inverse generic comparison.
`nearbySpecialization` specializes this map to `K = B^nr`, the pullback of the
arithmetic input `B`. The geometric specialization arrow is the first map of
the triangle in SGA 7 XIII, (1.4.2.2), pp. 97–98, with nearby cycles given by
(2.1.2.3), p. 99, and the specialization target displayed in (2.1.2.4), p. 100.
Laumon (1987), (2.3.2)–(2.3.2.1), pp. 159–160, uses the triangle and proper
pushforward. His (2.4.2)–(2.4.2.1), p. 162, gives the local Fourier charts and
compares their vanishing-cycle complexes by pullback.

`NearbySpecializationNaturalityStatement` gives the following equalities of
maps in the derived categories of pro-étale modules with condensed coefficients.

- Specialization is natural in the strict-chart complex. On the tensor unit
  it agrees with `NearbyCyclesModel.unit` via the derived pullback unit
  isomorphism along `i`. Both maps use the adjunction unit for `j`.
- For a compatible model morphism, pulling back specialization and then
  taking `Hom.pullbackExchange` agrees with first using the pullback comparison
  for the special square and then specializing the pulled-back complex.
  This is the specialization square for the comparison in SGA 7 XIII,
  (2.1.7.2), p. 101.
- Specializing the direct image on the total space and then applying
  `Hom.pushforwardExchange` agrees with first taking the mate for the special
  square and then taking the special-fibre direct image of specialization.
  The equality uses the exchange arrow for every compatible model morphism,
  including a proper map of strict charts as in SGA 7 XIII, (2.1.7.1), p. 101,
  and Laumon, (2.3.2.1), p. 160.
- For a Galois element preserving the chart base map, the special-fibre
  pullback of `nearbySpecialization` commutes with `nearbyCyclesAction`.
  On the special restriction of the input, the comparison uses the special
  square and the projection from the strict chart to the arithmetic chart.
  This realizes the transport of structure of SGA 7 XIII,
  (1.3.2.1)–(1.3.2.2), p. 94, which uses the geometric fibre diagram over the
  full normalization `S̄` of (0.2.5), p. 86. The geometric points factor
  through `S̄ → S^nr`. The chart here is over the pointed strict henselization
  `S^nr` of (2.1.3)–(2.1.4), p. 100, with the choice of points as in Laumon,
  (2.1.1), p. 151.
- Extension of coefficients along a map of commutative condensed rings gives
  a square of specialization arrows. On `Li*` its comparison is the derived
  pullback and extension-of-scalars isomorphism. On `Ψ`,
  `chartNearbyCyclesCoefficientMap` composes that comparison for `i`, the
  direct-image mate for `j`, and the pullback comparison for `ε`. This is the
  coefficient comparison of the same specialization construction.

## External declarations

At weil-conjectures commit `a25955cde4f85f67bef3149a6efc3efe20c22132`,
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each
of the following declarations. The model and derived operations are in
`AlgebraicGeometry.ProEtale.CondensedRing` unless qualified otherwise.

- `NearbyCyclesModel`, its projections `.i`, `.j`, `.ε`, `.nearbyCycles` and
  `.Hom` with `.Hom.total` are from `SixFunctors.NearbyCycles.Basic`.
  `NearbyCyclesModel.twistSpecializationMap` is from
  `TraceFormula.Specialization.NearbyCyclesTateTwist`. `NearbyCyclesModel.unit`,
  `.Hom.commSq_i`, `.Hom.pullbackExchange` and `.Hom.pushforwardExchange` are
  from `SixFunctors.NearbyCycles.Exchange`.
- `leftDerivedUpperStarCompOfEq` is from `SixFunctors.NearbyCycles.HomComp`.
  `leftDerivedUpperStarId`, `leftDerivedUpperStarUnitIso`,
  `derivedUpperStarLowerStarAdjunction` and `pullbackSquareComparison` are from
  `UpperStarCoherence`, `Monoidal`, `UpperLowerStar` and `Localizing` in
  `SixFunctors.ProEtale.ModuleObject.Derived`.
- `AlgebraicGeometry.ProEtale.coefficientMap`, `CategoryTheory.Mod.extendScalars`,
  `derivedUpperStarExtendScalarsIso` and `derivedUpperStarExtendScalarsPushHom`
  are used for the coefficient change. The comparisons come from
  `SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull` and `NonFlatPullCube`.
- `AlgebraicGeometry.ProEtale.condensedRingObj`, `upperStar`, `lowerStar`,
  `CategoryTheory.Functor.leftDerivedFunctor` and `.rightDerivedFunctor`
  give the coefficient objects, pullback and direct image with their derived
  functors. `CategoryTheory.sfbRegularAbMonoidal` and
  `CategoryTheory.sfbRegularAbSymmetric` are the instance names used in the
  elaboration attribute. `HasDerivedCategory.ofIsGrothendieckAbelian` from
  `CategoryTheory.GrothendieckAbelian.HasDerivedCategory` is the local
  derived-category instance.

Mathlib's `CategoryTheory.mateEquiv` forms the special-square direct-image
comparison and `AlgebraicGeometry.Scheme.ProEt.topology` supplies the topology.
Both use `[propext, Classical.choice, Quot.sound]`. The coefficient module
category `CategoryTheory.Mod` has no axiom dependencies.
