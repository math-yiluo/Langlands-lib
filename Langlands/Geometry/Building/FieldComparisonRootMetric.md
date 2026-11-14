# Canonical root metrics under actual field comparison

This internal construction equips the published split-torus reduced translation
base-change equivalence and literal apartment restriction with their canonical
root-metric isometries. The fields lie in an arbitrary common universe. No local
compactness of the extension field or descent of a chosen torus to a smaller
field is assumed.

For an affine group locally of finite type over a field, a split torus map,
and finite types of actual relative roots downstairs and upstairs,
`RootTranslationMetric.norm_splitTranslationBaseChange` states that the existing
`splitTranslationBaseChange` preserves the norm defined by the sum of squares
of all actual root forms. The existing `rootsBaseChangeEquiv` bijects those
root types, and `rootForm_splitTranslationBaseChange` identifies each summand.
Reindexing the finite sum gives equality of squared norms, hence of their
nonnegative square roots. The inverse norm identity follows by surjectivity.
`splitTranslationBaseChangeLinearIsometryEquiv` bundles this same linear
equivalence with its norm preservation. These assertions apply in particular
to field isomorphisms and involve no metric scaling.

For the published literal field restriction of a supplied upstairs apartment,
the original hypotheses remain explicit: a smooth affine ambient group, a
monomorphic split-torus map with opposite factor pairs, an upstairs unit
homomorphism to additive real values, and nontriviality on original units.
`rootForm_vsub_fieldRestrictAffineEquiv` identifies each original root form
on a restricted displacement with the actual base-changed root form on the
original upstairs displacement; this identity needs no finite-root assumption.
`norm_vsub_fieldRestrictAffineEquiv` proves that the actual affine restriction
preserves the root norm of every displacement. Its proof uses
`AffineMap.linearMap_vsub` and the published fact that the linear part is
inverse `splitTranslationBaseChange`. `isometry_fieldRestrictAffineEquiv` and
`fieldRestrictIsometryEquiv` give an isometry and an isometric equivalence for
any metrics whose distances equal those root norms on the apartments' original
affine differences. This explicit metric hypothesis prevents an unrelated
additive torsor structure from changing the meaning of the differences.

Finally, `vsub_reindexOrderApartment` shows that transporting an apartment
along an equality of field-order functions preserves the displacement itself.
Equality elimination reduces this assertion to reflexivity.
`isometry_reindexOrderApartment` then proves isometry for metrics realizing
the same canonical root norm.

The provenance is the published actual character, cocharacter and root
base-change comparison, literal apartment field restriction, field-order
equality transport, and root-coordinate norm construction. This unit only
adds their metric consequences and cites no additional external theorem.
It constructs neither a building metric nor an arbitrary coefficient action,
and asserts no coherence or finite-orbit result. Those remain obligations
of the unramified semilinear metric-action target.
