# First-order modules at every actual line bundle

This internal construction combines the published
`Picard.DualNumberPointedDeformations` and
`Picard.DualNumberDeformationModule` results. Its only additional argument
is translation in the actual line-bundle class group. It assumes no
external deformation or algebraicity theorem.

Let `k : Type u` be any field, `X : Scheme.{u}`, `f : X → Spec k`,
and `M` an actual line bundle on `X`. All constructions use the actual
dual-number thickening `thickening f`, its projection to `X`, and its
zero section `closedPoint f`. The tensor-preservation proof used by the
ordinary line-bundle class group is the Library theorem
`Modules.pullbackTensorComparisonIsIso`, imported from
`Modules.PullbackTensorProof`. It is proved rather than an extra premise.
Fixing this proof also lets typeclass search find operations on
`PointedDeformationClasses f M`, whose type contains no preservation
parameter.

`PointedDeformationClasses f M` is the set of isomorphism classes in the
actual groupoid of line bundles `L` on the thickening with a specified
isomorphism `M ≅ closedPoint^* L`. Its arrows are actual bundle
isomorphisms compatible with that specified reduction. The imported
`pointedClassEquiv` identifies these classes with the fibre of ordinary
pullback on line-bundle isomorphism classes over `[M]`. That equivalence
uses the already proved surjectivity of automorphism reduction; the
specified reduction is retained in the groupoid before passing to
isomorphism classes.

`splitLiftClass` is the ordinary class of `projection^* M` in this fibre.
The equation `closedPoint_projection` and functoriality of pullback prove
its reduction property. Write its class as `s`. The equivalence
`ordinaryTangentEquiv` sends an ordinary lift class `q` to `q s⁻¹`,
which lies in the kernel of zero-section pullback. Its inverse sends
`t` to `t s`. The two inverse identities are group cancellation.
`pointedTangentEquiv` composes this equivalence with `pointedClassEquiv`
and additive notation for that kernel.

`pointedClassesAddCommGroup` transports the kernel's tensor group along
this equivalence. `pointedTangentAddEquiv` proves that the equivalence is
additive for these operations. The explicit ordinary-class formulas
identify the resulting operations: zero has class `s`, and the sum of
pointed classes with ordinary classes `q` and `r` has ordinary class
`q r s⁻¹`. Thus the addition is normalized actual tensor product. These
constructions require no separatedness, quasi-compactness or properness.

`scaleOrdinaryLiftClass c` is actual ordinary pullback along the
thickening endomorphism `scale f c` induced by `ε ↦ c ε`.
`closedPoint_scale` proves that this pullback preserves the ordinary lift
fibre over `[M]`. `scale_projection` proves that it fixes `s`.
`pointedScaleClass` carries this operation to pointed isomorphism classes
through `pointedClassEquiv`. The displayed formula
`pointedScaleClass_ordinary_val`, also recorded as
`smul_pointedClasses_ordinary_val`, identifies its underlying ordinary
class with actual pullback. This defines an operation on pointed
isomorphism classes via the established bijection; the module does not
construct a new pullback functor on the pointed groupoid.

`pointedTangentEquiv_pointedScaleClass` proves that normalization commutes
with this scaling. The proof uses multiplicativity of actual pullback
and invariance of `s`. The target operation is the published scalar
operation on the trivial-bundle deformation kernel, itself actual
epsilon-scaling pullback, including at `c = 0`.

For separated, quasi-compact `f`, `pointedClassesModule` reflects the
known module laws along the injective additive normalization, using the
scaling equality just proved. `pointedTangentLinearEquiv` packages this
normalization as a `k`-linear equivalence. For each ordered affine cover
of `X`, `pointedTangentH1LinearEquiv` composes it with the published
linear comparison to actual derived structure-sheaf `H¹`.
`finrank_pointedClasses` is the resulting equality of finite ranks.

If `f` is proper, `finiteDimensional_pointedClasses` transfers the
published finite dimensionality of the trivial-bundle deformation module
along the inverse linear normalization. Properness supplies the
separatedness and quasi-compactness used by the module construction.
This holds at every actual line bundle, over arbitrary possibly imperfect
fields, including empty or nonreduced proper schemes. There is no
projectivity, smoothness, connectedness, rational point or global-functions
hypothesis.

The result concerns actual pointed dual-number isomorphism classes.
Comparison with the relative Artinian-test pseudofunctor, formal versality,
effectivity, algebraization, openness of versality and existence of a
smooth atlas are further obligations. This module proves none of those
existence statements.
