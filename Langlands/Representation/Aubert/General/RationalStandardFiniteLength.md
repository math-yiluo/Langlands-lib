# Dynamic finite length on the actual standard rational-point families

Author: Worker 749. Worker 508 contributed the companion generic helper
[`Aubert.General.SharpFiniteLength`](SharpFiniteLength.md), whose termwise
premise this module is meant to supply. This module does not import it.

This is a derived internal adapter. It states no new target. It proves that the
two dynamic finite-length statements of
[`Aubert.General.PrerequisiteStatements`](PrerequisiteStatements.md) give
finite-length preservation for the actual normalized functors of every standard
rational-point decomposition. These are the decompositions used by
`RationalSharpFiniteLengthStatement`. The two dynamic statements remain explicit
hypotheses here; this module proves neither of them.

## Transport along equal subgroups

The first section works with an arbitrary locally compact nonarchimedean group
`G : Type uG` and an arbitrary carrier universe `uV`.

- `jacquetFunctor_preservesFiniteLength_of_eq` and
  `normalizedInductionFunctor_preservesFiniteLength_of_eq` take two semidirect
  decompositions `P = M ⋉ U` and `P' = M' ⋉ U'` with closed radicals and
  equalities `P = P'`, `M = M'`, `U = U'`. They transfer finite-length
  preservation from the actual normalized Jacquet, respectively induction,
  functor of the primed decomposition to that of the unprimed one.
  `IsSemidirectDecomposition` and `IsClosed` are propositions, so after
  substituting the equalities both functors are built from the same subgroups
  and the hypothesis applies directly.
- `inductionJacquetFunctor_preservesFiniteLength` shows that the composite
  `inductionJacquetFunctor h hU = jacquetFunctor ⋙ normalizedInductionFunctor`
  of [`Aubert.General.Parabolic`](Parabolic.md) preserves finite length when
  both factors do at the saturated carrier universe `max uG uV`. The proof is
  the published `SmoothRep.PreservesFiniteLength.comp`.

## The standard families

The second section fixes the data of the actual standard families of
[`Aubert.General.RationalPointFamily`](RationalPointFamily.md): a field
`k : Type u`, a commutative group scheme `T` and a group scheme `G` over
`Spec k` with affine structural morphism, `i : T.toGrp ⟶ G`, a cocharacter `ν`,
`hStandard : StandardCocharacterStatement.{u}`, connected reductivity `hG`, a
maximal split torus `hi` and genericity `hν`. Finite subsets `I` of
`SimpleRoot i ν` index the published subgroups `parabolic i ν I`,
`levi i ν I` and `unipotent i ν I`. Their decomposition is the published
`isSemidirectDecomposition_of_standardCocharacterStatement` of
[`Aubert.General.RationalParabolicDecomposition`](RationalParabolicDecomposition.md).
The topology on `G(k)` is the published `pointTopology`. The finite-length
results also assume that `G(k)` is locally compact and nonarchimedean and that
every `unipotent i ν I` is closed. These are the hypotheses
`RationalSharpFiniteLengthStatement` provides.

- `RationalPointFamily.standardDynamicCocharacter i ν hStandard hG hi hν I` is
  the composite `CommGroupScheme.groupHom ζ ≫ i`, where `ζ` is a standard
  cocharacter of `rootSet i ν I` chosen by `Classical.choose` from the
  existence part of `hStandard`. It is the only definition of the module and
  serves the following lemma. Its value depends on the choice; only the three
  subgroup equalities below are used.
- `RationalPointFamily.standardDynamicCocharacter_eq` applies the comparison
  part of `hStandard` to this `ζ`. It identifies `parabolic i ν I`,
  `levi i ν I` and `unipotent i ν I` with the rational points of
  `Dynamic.parabolic χ`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ` for
  `χ = standardDynamicCocharacter i ν hStandard hG hi hν I`. The definition
  and this lemma need only that `k` is a field; they use none of the
  local-field or topological hypotheses.
- `RationalPointFamily.standardJacquet_preservesFiniteLength_of_dynamic`
  assumes `DynamicJacquetFiniteLengthStatement.{u, uV}`. It concludes that
  the actual normalized Jacquet functor of the standard decomposition of `I`
  preserves finite length at carrier universe `uV`. The closedness hypothesis
  for `unipotent i ν I` is moved along the equality to `Dynamic.unipotent χ`.
  The dynamic statement is applied to `χ` with the decomposition
  `dynamic_isSemidirectDecomposition`. The result is transferred back by the
  first transport lemma.
- `RationalPointFamily.standardInduction_preservesFiniteLength_of_dynamic`
  is the same argument for `DynamicInductionFiniteLengthStatement.{u, uV}` and
  the actual normalized induction functor.
- `RationalPointFamily.standardInductionJacquet_preservesFiniteLength_of_dynamic`
  assumes both dynamic statements at carrier universe `max u uV`. It concludes
  that the actual composite `inductionJacquetFunctor` of every standard
  decomposition preserves finite length.

At `uV := max (u + 1) v`, the last theorem gives the premise `hfl` of
`sharpFiniteLengthTarget_of_inductionJacquet` for the families in
`RationalSharpFiniteLengthStatement.{u, v}`. The hypotheses
`IsSemidirectDecomposition` and `IsClosed` there are propositions, so any
proofs of them yield the same functor. This module does not import
`SharpFiniteLength` and does not prove the rational target.

## Provenance and scope

The proofs are elementary transport along subgroup equalities and composition
of functors. They use no representation theory beyond the two hypotheses. The
dynamic statements are the Library's formalizations, recorded in
`PrerequisiteStatements`, of Renard, *Représentations des groupes réductifs
p-adiques* (French edition of 9 July 2026), VI.6.2 and VI.6.4, printed
pp. 178–179 (PDF pp. 184–185). Here they are hypotheses, not results. The standard-to-dynamic comparison is exactly the published
`StandardCocharacterStatement` of
`Langlands.GroupScheme.Rational.StandardCocharacterStatement`, which is also
a hypothesis. No new instance of it is proved.

Declarations reused by name: `jacquetFunctor`,
`normalizedInductionFunctor` and `inductionJacquetFunctor`
(`Aubert.General.Parabolic`) and `dynamic_isSemidirectDecomposition`
(`Aubert.General.DynamicParabolic`), both by Worker 23; the standard families
`parabolic`, `levi`, `unipotent` and `rootSet`
(`Aubert.General.RationalPointFamily`);
`isSemidirectDecomposition_of_standardCocharacterStatement` (Worker 165,
`Aubert.General.RationalParabolicDecomposition`); the two dynamic statements
(Worker 1180, `Aubert.General.PrerequisiteStatements`), and
`SmoothRep.PreservesFiniteLength` with its `comp` lemma
(`Representation.Smooth.FiniteLengthGrothendieckFunctor`). No imported pair
is changed.
