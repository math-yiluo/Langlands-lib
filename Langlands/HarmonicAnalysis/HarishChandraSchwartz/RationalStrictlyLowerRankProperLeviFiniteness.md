# Strictly lower-rank finiteness supplies the proper-Levi interface

This derived adapter connects the published rank-restricted local VIII.1.2
predicate to the published `RationalSemistandard.ProperLeviOrbitFiniteness`
predicate. It packages the existing pointwise specialization without changing
either predicate or requiring finiteness at the ambient group.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), printed p.321 (PDF p.87), the induction
paragraph preceding VIII.2 and the use of VIII.1.2 and VIII.1.3 on proper
Levis. Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The paper supplies the reason for using strictly smaller semisimple ranks;
the explicit interface packaging and vacuity proof here are derived content.

The field is any nonarchimedean local field in the Library convention, which
includes finite residue field. The ambient group is connected reductive;
its affineness and local finite type follow from reductivity. There is no
restriction on characteristic, splitting, quasi-splitness or positive rank.
The field universe `u` and representation-carrier universe `uV` are independent.
The imported local predicate uses actual rational points, their canonical
topology and the complex smooth representation category.

## Declarations and implemented proofs

All declarations are in `Langlands.HarishChandraSchwartz`.

| Declaration | Exact content | Implemented proof or status |
| --- | --- | --- |
| `RationalStrictlyLowerRankProperLeviFinitenessStatement` | For every indicated field, connected reductive group and maximal split torus `i`, local orbit finiteness for groups of actual `relativeRootRank` strictly below `relativeRootRank i` implies `RationalSemistandard.ProperLeviOrbitFiniteness (i := i)`. | Prop-valued conditional target, established by the final theorem under the separate structural rank-decrease premise. |
| `properLeviOrbitFiniteness_of_strictlyLowerRank` | The same implication at one group and torus, retaining `SemistandardProperLeviRankStatement` explicitly. | Introduces each proper intrinsic index and every closed connected reductive model of its literal Levi, then applies the published `rationalLocalOrbitFiniteness_properLevi_of_lowerRank`. The resulting local predicate is definitionally the owner's `LeviModel.LocalOrbitFiniteness`. |
| `properLeviOrbitFiniteness_of_rank_zero` | At relative semisimple rank zero, the proper-Levi premise holds under the same structural comparison without an analytic premise. | The published `semistandardParabolic_eq_top_of_rank_zero` contradicts properness of each putative index, so the universal predicate is vacuous. |
| `rationalStrictlyLowerRankProperLeviFiniteness` | Establishes the packaged conditional target from `SemistandardProperLeviRankStatement`. | Introduces the global field, group and torus arguments and applies the first specialization theorem. |

Properness is precisely inequality of the index's all-test parabolic subgroup
functor with the whole group. The proper-Levi predicate retains every actual
closed reductive representing model, every split component of that model,
every quotient Haar measure and every compact open level. It does not replace
these quantifiers by selected family data or by standard parabolics.

The rank is the dimension of the span of the actual relative roots, not the
full split-torus rank. The imported pointwise theorem lifts the ambient maximal
split torus through the model's closed representing inclusion and applies the
restricted finiteness premise at that actual torus. Its strict rank decrease is
exactly the displayed structural premise. In a well-founded induction on
natural-number rank, only hypotheses for strictly smaller groups are used.
The rank-zero result concerns semisimple rank zero and the empty proper part.

## Dependency boundary

This unit imports `RationalStrictlyLowerRankOrbitFiniteness` and
`RationalSemistandardThetaFixed`. It leaves their definitions and statements
unchanged. The structural rank-decrease assertion remains an explicit open
target; the adapter proves no new structural rank theorem.

The conclusion is the local finiteness premise for the proper support
interface. Actual proper Fourier support still requires that interface's
separate support and fixed-level comparisons. Local synthesis reconstruction
is a distinct lower-rank input for detecting zero induced constant terms and
does not occur here. This unit constructs no Fourier family, synthesis,
inverse or projection, and uses no same-rank finiteness or Plancherel premise.
