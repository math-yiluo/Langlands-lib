# Woundness of the ordinary radical modulo the split radical

`Langlands.GroupScheme.splitRadicalWoundQuotient.{u}` proves exactly the
published proposition `SplitRadicalWoundQuotientStatement.{u}`. For every
field and every supplied smooth connected affine ambient group, ordinary
unipotent radical, split unipotent radical, commuting inclusion and smooth
connected affine fppf quotient, every affine-line morphism into that quotient
is constant at a rational value. The statement and its imported definitions
are unchanged. The theorem has no additional premise.

The proof first supplies the full central additive-subgroup criterion by
applying `UnipotentWoundCriterionReduction.criterion_of_vectorFactor` to
the unconditional `RelativeRoot.commutativePTorsionVectorFactor`. That
consumer includes the characteristic-zero branch and the prime-characteristic
central-family argument. Applying `woundSeparableFromCriterion` to the
result supplies separable algebraic invariance of affine-line constancy.
Thus both geometric statements used below are proved inside the assembly
from published results, rather than assumed.

Choose a split radical `w : W ⟶ U` of the supplied ordinary radical `U`
over the original field. The normal-subgroup quotient theorem provides
an actual smooth connected affine quotient `r : U ⟶ R`.
`IsSplitUnipotentRadical.hasConstantAffineLineMaps_quotient_of_criterion`
makes `R` wound using the criterion just proved and the unipotence of `U`.
The quotient is unipotent, so separable invariance makes its actual
pullback to `SeparableClosure k` wound as well.

The supplied normal inclusion `j : U ⟶ G` defines the actual conjugation
action of `G` on `U`. Over the separable closure, smoothness gives dense
rational points on the product of the changed ambient group and `W`,
using `hasDenseRationalPoints_of_smooth_of_isSepClosed`.
`AutomorphicAction.onSplitKernelOfWoundBaseChange` applies split-source
rigidity to the changed quotient and descends the action to `W`.
Its compatibility with inclusion and the original conjugation action
proves normality of `w ≫ j` on every relative scheme test.

Greatestness of the supplied ambient split radical `n : V ⟶ G` now
places `W` inside its image. The supplied equation `m ≫ j = n` and
monicity of `j` place the image of `w` inside that of `m : V ⟶ U`.
Greatestness of `w` among normal split subgroups of `U` then proves the
corresponding greatestness for `m`. Closedness of `m` follows from
closedness of its composite with `j`; smoothness, connectedness and the
two unipotence properties come from the supplied split radical.
Normality follows by pulling back the full image of `n` along the monic
map `j`, using `range_comp_comap_of_mono`.

Consequently `m` itself satisfies `IsSplitUnipotentRadical`. The same
central-criterion quotient reduction applies directly to the supplied
`q : U ⟶ Q` and its supplied fppf kernel equality, giving
`HasConstantAffineLineMaps Q`. The auxiliary quotient `R` is used only
to prove normality of `W`; the conclusion concerns the original `Q`.

All constructions retain arbitrary universe `u`, finite and imperfect
fields, and characteristic zero. Normality, subgroup containment and
quotient kernel equality use every relative scheme test, including
nonaffine and nonreduced tests. No lift, quotient section, structural
comparison premise or pre-existing woundness premise is added.

This is an internal proof assembly of the published target, whose
Markdown records its provenance in CGP Corollary B.3.5 and the additional
characteristic-zero scope. The implemented route uses the named
central-criterion reduction, actual actions, smooth separably closed
density and fpqc descent. Worker 1608 authored this assembly; the
prerequisites are imported from the published Library.
