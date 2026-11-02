# Stack transport for actual relative line bundles

For every morphism `f : X ⟶ S` of schemes, this module proves the relative
stack property from the global stack property of the actual line-bundle
pseudofunctor. There is no restriction on `f`.

The construction
`PicardGroupoid.relativeDescentDataEquivalence f g` identifies the full
descent category of `PicardGroupoid.relative f` for a family
`g i : U i ⟶ T` in `Over S` with the full descent category of
`PicardGroupoid.pseudofunctor` for the mapped family
`(relativeSpace f).map (g i)`. The objects of the mapped family are the
actual schemes `U i ×_S X`. The equivalence specializes
`StackPullback.descentDataEquivalence` using the chosen pair and triple
pullbacks supplied in `StackTransport`. It retains the unrestricted descent
data and their compatible component morphisms.

The lemma `PicardGroupoid.relative_isStack f J` states that, for every
Grothendieck topology `J` on schemes, a stack structure on
`PicardGroupoid.pseudofunctor` for `J` implies a stack structure on
`PicardGroupoid.relative f` for `J.over S`.
`PicardGroupoid.relative_isStack_fpqc f` specializes this to the fpqc
topology. All these declarations are uniform in the scheme universe `u`;
the family-index universe `t` in the descent-category equivalence is
independent of `u`.

Two preservation facts make the specialization possible. First,
`relativeSpace f` is `Over.pullback f ⋙ Over.forget X`.
The slice pullback functor is a right adjoint, so preserves pullbacks.
The forgetful functor preserves connected limits, hence pullbacks.
The shared instance `relativeSpace_preservesPullbacks` in
[`RelativeGeometry`](RelativeGeometry.md) obtains preservation for the
composite from these Mathlib instances. Second, for any `J`,
Mathlib proves cover preservation of the slice pullback functor from
`J.over S` to `J.over X` and of the forgetful functor from `J.over X` to
`J`. The lemma `relativeSpace_coverPreserving` composes these facts.

Applying `StackPullback.isStack_reindex` proves the relative stack result.
The published definition of `PicardGroupoid.relative` is exactly the
reindexed pseudofunctor appearing in that theorem. The canonical
global-to-descent functor compatibility established in `StackTransport`
therefore supplies both descent of morphisms and effective descent of
objects for this actual pseudofunctor with its specified coherence.

This is an internal specialization of the categorical constructions in
`StackPullback` and `StackTransport` to the published `Groupoid` and
`RelativeGeometry` definitions. Its preservation inputs are the pinned
Mathlib declarations `Over.mapPullbackAdj`,
`Over.preservesLimitsOfShape_forget_of_isConnected`,
`GrothendieckTopology.coverPreserving_overPullback`, and
`GrothendieckTopology.over_forget_coverPreserving`. It is not a
translation of a separate literature assertion. The global fpqc stack
property remains an explicit hypothesis; this module does not by itself
prove `LineBundleFpqcStackStatement`.
