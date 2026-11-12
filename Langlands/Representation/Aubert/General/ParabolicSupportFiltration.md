# Support filtration of Jacquet restriction after parabolic induction

Module: `Langlands.Representation.Aubert.General.ParabolicSupportFiltration`,
namespace `Langlands.Aubert.General`. Author: Worker 4021.

This module filters the composite `r_Q ∘ i_P` of normalized parabolic induction
and normalized Jacquet restriction. The filtration is by the images of the
functions supported on initial unions of an ordered orbit cover. Each successive
quotient is identified, naturally, with the normalized radical coinvariants of
the compact Mackey orbit piece. It is the support-filtration and exactness part
of the geometric lemma, for arbitrary actual semidirect subgroup triples. It
does not identify the orbit pieces with normalized intersection functors, and it
does not construct an ordered orbit cover. Both are separate steps.

## Setting

`G` is a group with a topology, `LocallyCompactSpace` and `NonarchimedeanGroup`.
`P M U Q L V` are subgroups of `G`, with actual semidirect decompositions
`dP : IsSemidirectDecomposition P M U` and `dQ : IsSemidirectDecomposition Q L V`.
`U` and `V` are closed (`hU`, `hV`). These are the hypotheses of the published
`normalizedInductionFunctor dP hU` and `jacquetFunctor dQ hV` (module
`Aubert.General.Parabolic`). No reductive structure is used. The group universe
`uG` and the carrier universe `uV` are independent.

## Declarations

- `parabolicInducingFunctor dP hU : SmoothRep ℂ M ⥤ Rep ℂ P` is
  `inflationFunctor dP` followed by the twist by
  `inductionCharacter U P hU _`, the positive half Haar character of `U` on `P`.
  `normalizedInduction_restrict_eq` records, by `rfl`, that normalized induction
  restricted to `Q` is `Geometric.rawRestrictedSmoothInduction P Q` applied to
  this covariance. So the published normalized induction is used unchanged.
- `inductionSupportFiltration dP hU s` is the published
  `OrderedDoubleCosets.rawSmoothSupportFiltration s`, precomposed with the
  inducing functor. Here `s : Geometric.OrderedDoubleCosets P Q m` is any
  ordered orbit cover. It filters normalized induction, restricted to `Q`.
- `isSmooth_parabolicInducingFunctor_obj` and `smoothParabolicInducingFunctor`
  give the same covariance in the full smooth category of `P`. They assume that
  the Levi projection `dP.projection` is continuous.
- `parabolicInverseHalfCharacter dQ hV` is the inverse half Haar character
  `HaarModulus.closedInverseHalfCharacter V hV L _`, as a smooth character of `L`.
  `parabolicCoinvariantsFunctor dQ hV : Rep ℂ Q ⥤ Rep ℂ L` takes
  `Jacquet.Localization.functor` for `V.subgroupOf Q` with the trivial character.
  It restricts the action to `L` and twists by this character.
  `parabolicCoinvariantsRestrictionIso` compares it with the published
  `jacquetFunctor dQ hV` on ambient smooth representations restricted to `Q`.
  The comparison is `Jacquet.Localization.transportEquiv` along
  `V.subgroupOf Q ≃* V`. It sends the class of `v` to the class of `v`.
- `smoothParabolicCoinvariantsFunctor` bundles smoothness of these coinvariants.
  `smoothParabolicCoinvariantsFunctor_exact` proves exactness on the full smooth
  category of `Q` when `V.subgroupOf Q` is a limit of compact subgroups. It uses
  the published injectivity, middle exactness and surjectivity of character
  localization.
- `jacquetImageSubfunctor dP hU dQ hV S` maps a natural `Q`-stable subspace `S`
  of normalized induction to its image in the `V`-coinvariants. It uses the
  published `CorrectedFiltration.jacquetImage`.
  `jacquetSupportFiltration dP hU dQ hV s` applies it to every step of the
  support filtration. The result is a `RepFunctorFiltration` of the actual
  composite
  `normalizedInductionFunctor dP hU ⋙ jacquetFunctor dQ hV ⋙ SmoothRep.toRep`.
  Its zero step is the image of zero. Its top step is everything, because the
  coinvariant quotient map is surjective.
- `jacquetImage_eq_isoTransport_exactImage` shows that this image subfunctor is
  exactly the transport, along `inductionCoinvariantsRestrictionIso`, of the
  invariant image of the mapped smooth inclusion.
  `jacquetImageQuotientIso` and `jacquetSupportGradedIso` then apply the
  published `RepSubfunctor.exactImageQuotientIso` to exactness. They identify
  each successive quotient of `jacquetSupportFiltration` with
  `parabolicCoinvariantsFunctor dQ hV` of the corresponding successive quotient
  of `inductionSupportFiltration`. This uses that `V.subgroupOf Q` is a limit
  of compact subgroups.
- Assume `CompactSpace (Induction.LeftQuotient P)`.
  `inductionSupportCompactIso` is the published
  `OrderedDoubleCosets.rawSupportGradedCompactSmoothIso`, whiskered by the
  inducing functor. It identifies the compact and smooth support quotients.
  Assume further that `G` is Hausdorff and sigma-compact and that `P` and `Q`
  are closed. `inductionSupportOrbitIso` composes this with the published
  natural isomorphism of `Geometric.closedSubgroupMackeyFiltration`. The
  induction support grade at `i` becomes
  `smoothParabolicInducingFunctor ⋙ Geometric.orbitPiece P Q (s.representative i)`.
  That is compact induction from the orbit stabilizer `Q ∩ w P w⁻¹` of the
  covariance pulled back along `q ↦ w⁻¹ q w`, where `w = s.representative i`
  and the orbit is that of `P w⁻¹`.
- `jacquetSupportOrbitIso` combines the two steps. The `i`th successive quotient
  of `jacquetSupportFiltration` is naturally isomorphic to
  `smoothParabolicInducingFunctor ⋙ Geometric.orbitPiece P Q (s.representative i)
  ⋙ parabolicCoinvariantsFunctor dQ hV`.

All isomorphisms are natural isomorphisms of functors on the full category of
smooth complex representations of `M`. No admissibility, finite length or
dimension condition is imposed.

## Provenance

This is a derived construction. Mathematically it is the support-filtration
step of the geometric lemma: Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, Sections 5.1–5.4, printed pp.459–461; and
Renard, *Représentations des groupes réductifs p-adiques* (2026), registered as
`renard-2026-representations-groupes-reductifs-padiques`, VI.5.1, printed
pp.163–164 / PDF pp.169–170 (support filtration and exactness of the Jacquet
functor) and printed p.171 / PDF p.177 (the stabilizer). The Lean route adapts
the published represented-parabolic modules
`Geometric.RepresentedParabolicSupportFiltration`,
`Geometric.RepresentedParabolicCoinvariants`,
`Geometric.RepresentedParabolicCoinvariantsExact`,
`Geometric.RepresentedParabolicSupportOrbit` and
`Geometric.RepresentedParabolicSupportJacquet` to arbitrary subgroup triples,
so that they apply to the rational standard families of the Aubert program.
The proofs use only the published support filtrations, the
compact-to-smooth comparison, the closed-subgroup Mackey theorem, exactness of
character localization and the filtration transport lemmas. They use no
geometric lemma, adjointness, cuspidal support, character independence or
Langlands classification.
