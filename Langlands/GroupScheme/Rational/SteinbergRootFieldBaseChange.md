# Actual field extension of supplied normalized root maps

This is internal infrastructure derived from the Library's actual group-scheme
pullbacks, intrinsic root subgroups, Lie scalar extension, and standard
vector-group comparison. It uses no additional literature assertion or
existence theorem for normalized root maps.

Fix arbitrary fields `k` and `F` in one arbitrary universe, an algebra structure
`Algebra k F`, an affine group scheme `G` over `k`, a supplied split pinning
`p`, a simple root `a` of its supplied base, and a supplied normalized root
parametrization `x` at `a`.

`VectorGroup.baseChangePointsEquiv_scalarPoint_inv` proves that the inverse
standard vector-group comparison projects a scalar point with coordinate `c`
to the original scalar point with the same global function `c`. It holds on
every scheme test over `F`. The proof applies the injective coordinate
equivalence and the coordinate formula for the forward comparison.

`NormalizedRootParametrization.fieldBaseChangeHom` first applies that inverse
comparison to the standard line over `F`, then applies the actual pullback of
`x.hom`. Its all-test evaluation formula `fieldBaseChangeHom_point` identifies
the projected point with `x.point` on the corresponding test over `k`.
`fieldBaseChangeHom_isClosedSubgroup` proves closedness by pullback stability
and composition with the source isomorphism. Neither construction nor these
point and closedness formulas require algebraicity of the field extension.

`fieldBaseChangeHom_represents` additionally assumes `Algebra.IsAlgebraic k F`
and states that this map represents the whole intrinsic simple-root subgroup
for the actual transported split pinning `p.baseChange`, at the index
`p.baseChangeSimpleEquiv a`. It uses the intrinsic root-subgroup base change
formula, pullback of the original represented subgroup, and invariance of a
homomorphism's range under precomposition with a source isomorphism. The
algebraicity assumption is retained by the assembled split-pinning API.

`fieldBaseChangeHom_torus_equivariant` proves the root-weight formula on every
scheme test for the actual pulled-back torus, inclusion and character. It
requires no algebraicity assumption. Applying the injective pullback-point
equivalence reduces the formula to `x.torus_equivariant`; character values
are exactly preserved by the character pullback comparison.

`fieldBaseChangeHom_derivative` also holds for an arbitrary field extension.
Its value on the normalized epsilon vector is exactly
`Lie.schemeScalarExtension G (1 tensor p.pinning.rootVector a)`. Affine local
finite type needed for the scalar-extension comparison follows from the given
split pinning's smooth connected reductive group. The proof rewrites the new
epsilon as the image of the scalar-extended old epsilon under the standard
comparison, composes the actual differentials, cancels the source isomorphism,
and applies the original derivative normalization and the pure-tensor
naturality of `Lie.targetMapLinear` under actual scalar extension.

Finally, `NormalizedRootParametrization.fieldBaseChange` assembles these laws
into a normalized parametrization for `p.baseChange` at the transported simple
root, assuming `Algebra.IsAlgebraic k F`. Its derivative field uses the exact
`SplitPinning.baseChange_rootVector` formula. Thus it transports the supplied
map and its prescribed derivative, with no arbitrary choice of root maps.
No characteristic, perfectness, infinitude, or algebraic-closedness restriction
is made. Reflection representatives, ordered Steinberg products and the
quotient-isomorphism theorem are separate subsequent work.
