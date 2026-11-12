# The parabolic orbit piece as the normalized compact orbit source

Module: `Langlands.Representation.Aubert.General.RationalGeometricOrbitSource`,
namespace `Langlands.Aubert.General`. Author: Worker 4021.

`ParabolicSupportFiltration` filters `r_Q ∘ i_P`. Its published
`jacquetSupportOrbitIso` identifies the successive quotient at an orbit `P w⁻¹ Q`
with

`smoothParabolicInducingFunctor dP hU hp ⋙ Geometric.orbitPiece P Q w ⋙ parabolicCoinvariantsFunctor dQ hV`.

This module rewrites that composite as compact induction from the literal
target-intersection parabolic, followed by Mathlib's normal coinvariants of the
kernel of the Levi projection. For the actual rational standard family, the
result is literally the published `geometricNormalizedCompactSourceFunctor`
(module `RationalGeometricNormalizedCompactFunctor`). Composing with the
published `geometricNormalizedCompactActualNatIso` then reaches the
epsilon-twisted compact geometric term.

This is plumbing. It involves no Haar computation, no epsilon cancellation, no
compact/full induction comparison and no orbit ordering. Those are separate
steps.

## Generic declarations

The setting is a group `A` with a topology, `LocallyCompactSpace` and
`NonarchimedeanGroup`. It has subgroups `PI MI UI PJ MJ UJ`, actual semidirect
decompositions `dI : IsSemidirectDecomposition PI MI UI` and
`dJ : IsSemidirectDecomposition PJ MJ UJ`, closed radicals `hUI` and `hUJ`, and
a point `n : A`. Everything is stated over this abstract group. One reason is
generality. The other is that kernel checks never reduce the group law of scheme
points.

- `compactInducedSubgroupEqEquiv` transports compact induction along an
  equality of inducing subgroups, given pointwise equal coefficient actions.
  The functions are unchanged (`compactInducedSubgroupEqEquiv_eval`).
  `compactInducedSubgroupEqEquiv_map` shows that the transport commutes with
  compact induction of intertwining maps that have the same underlying linear
  map.
- `IsSemidirectDecomposition.ker_projection_eq` proves that the kernel of the
  Levi projection `dQ.projection` is `V.subgroupOf Q`.
- `normalParabolicCoinvariantsFunctor dQ hV : Rep ℂ Q ⥤ Rep ℂ L` is built in
  three steps. It takes Mathlib's normal coinvariants `π.ρ.toCoinvariants
  dQ.projection.ker`, restricts along `Subgroup.inclusion dQ.levi_le`, and
  twists by `HaarModulus.closedInverseHalfCharacter V hV L _`.
  `parabolicCoinvariantsNormalIso` is a natural isomorphism from the published
  `parabolicCoinvariantsFunctor dQ hV` to this functor. The published functor
  uses the character-one localization of `V.subgroupOf Q`. Each component
  combines three existing comparisons:
  `Jacquet.Localization.Coefficient.normalCoinvariantsLocalizationEquiv`,
  `normalCoinvariantsCongr` along `ker_projection_eq`, and `twistEquiv` of the
  same inverse half character. Vector classes are preserved.
- `orbitStabilizer_eq_geometricTarget` proves that the stabilizer
  `Geometric.orbitStabilizer PJ PI n`, i.e. the set of `q` with
  `n⁻¹ q n ∈ PJ`, equals
  `(geometricTargetIntersection PI PJ n).subgroupOf PI`, i.e. `P_I ∩ n P_J n⁻¹`
  read inside `P_I`.
- `geometricCompactInducingFunctor dJ n hUJ : SmoothRep ℂ MJ ⥤ Rep ℂ PI` sends
  `σ` to compact induction, from that target intersection, of
  `(twist χ σ).comp f`. Here `χ` is the closed half character of `UJ` on `MJ`
  and `f = geometricCoefficientProjection PI PJ MJ UJ dJ n`, i.e.
  `x ↦ pr_J(n⁻¹ x n)`. Morphisms go to the corresponding compact induction maps.
- `orbitPiece_coefficient_eq` compares two coefficients on stabilizer points.
  The inducing covariance of normalized induction, `twist δ_{UJ,PJ}^{1/2}
  (σ ∘ pr_J)`, composed with `stabilizerToInducing`, agrees with
  `(twist χ σ).comp f`. The proof uses the published
  `closedHalfCharacter_eq_comp_projection`. That lemma needs `UJ` to be
  unimodular, which follows from
  `isUnimodularModulus_of_isLimitOfCompactSubgroups` and the premise
  `hUJc : IsLimitOfCompactSubgroups UJ`.
- `orbitPieceInducingIso` is a natural isomorphism from
  `smoothParabolicInducingFunctor dJ hUJ hprojJ ⋙ Geometric.orbitPiece PJ PI n`
  to `geometricCompactInducingFunctor dJ n hUJ`. Its components are
  `compactInducedSubgroupEqEquiv`, and they keep the same functions.
- `orbitPieceCoinvariantsIso` composes the previous isomorphism with
  `parabolicCoinvariantsNormalIso dI hUI`. It gives

  `smoothParabolicInducingFunctor dJ hUJ hprojJ ⋙ Geometric.orbitPiece PJ PI n ⋙ parabolicCoinvariantsFunctor dI hUI ≅ geometricCompactInducingFunctor dJ n hUJ ⋙ normalParabolicCoinvariantsFunctor dI hUI`.

## Rational specialization

`RationalPointFamily.geometricNormalizedCompactSourceRepIso` covers the actual
standard families `parabolic i ν`, `levi i ν`, `unipotent i ν` with the
original decompositions `dI`, `dJ` and an actual torus-normalizer point `n`.
It is a natural isomorphism from
`geometricNormalizedCompactSourceFunctor … ⋙ SmoothRep.toRep` to
`geometricCompactInducingFunctor dJ n hUJ ⋙ normalParabolicCoinvariantsFunctor dI hUI`.
Its components are identities: the published source is defined as
`twist κ ((toCoinvariants (compactInduced H ((twist χ σ).comp f)) dI.projection.ker).comp s)`,
and this is the generic composite on the nose. The declaration keeps every
hypothesis of the published source functor.

## Provenance and dependencies

This is an internal derived construction. It lets the generic support
filtration feed the rational normalized compact comparison. Mathematically,
it is the identification of the Mackey orbit piece with `ind_{P_I ∩ n P_J n⁻¹}^{P_I}`
of the conjugated coefficient, followed by Jacquet coinvariants. This is
BZ77 5.2 and Renard VI.5.1, printed p.171. The proof bodies use the published
declarations named above, together with extensionality and categorical
composition. They use no geometric-lemma expansion, adjointness, cuspidal
support, character independence or Langlands classification. The imported
module closure is larger.
