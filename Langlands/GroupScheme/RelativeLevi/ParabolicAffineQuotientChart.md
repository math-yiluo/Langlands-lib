# Smooth proper affine-base parabolic quotient charts

For any base scheme `S`, let `G` be reductive and `i : P ⟶ G` an actual relative
parabolic. If an actual homogeneous right-coset quotient `Q` is supplied and
`range i` equals its full normalizer subgroup functor, `homogeneousQuotientChart`
is a natural transformation from the scheme Yoneda presheaf of `Q.scheme` into
the actual parabolic presheaf. It uses the smooth surjective projection carried
by `HomogeneousQuotient` and rewrites its exact all-test right-coset fiber
criterion using the self-normalizer equality.

`homogeneousQuotientChart_app_comp` identifies evaluation at `g ≫ Q.projection`
with the actual conjugate parabolic associated to `g`. The general quotient
chart's injectivity and monicity give `homogeneousQuotientChart_injective` and
`homogeneousQuotientChart_mono`. In particular,
`homogeneousQuotientChart_existsUnique_conjugate` proves that every conjugate
with a supplied group-valued parameter has exactly one parameter in `Q.scheme`.
It uses the projection for existence and all-test injectivity for uniqueness;
it does not require every quotient point to have a global group-valued lift.

For `S = Spec R` with `R` any commutative ring, the module constructs this data
from `hG : IsReductive G` and `hi : IsRelativeParabolicSubgroup i`, with no
additional subgroup or geometric premises. `affineParabolic_normalizer_eq`
applies the published ring-base self-normalizer theorem. Its closedness input
comes from `relativeParabolicClosed`; its smoothness input is `hi.smooth`; and
its field-algebra parabolicity input follows from
`hi.isParabolicSubgroup_baseChange` at `Spec.algebraMap R k`.

`affineParabolicQuotient` constructs an actual `ProperHomogeneousQuotient i` by
applying `properQuotientOfDynamicAndAmbient` to the published proofs
`parabolicDynamic` and `selfNormalizingProperAmbient` and those same verified
subgroup hypotheses. Thus its quotient carries a smooth surjective projection,
exact right-coset fibers on every test scheme, and a proper structure morphism.
`affineParabolicQuotient_smooth` descends the ambient group's smoothness along
that projection, using `RelativeParabolicQuotientFibers.smooth`.
`affineParabolicChart` is the associated actual natural chart, and
`affineParabolicChart_mono` proves its monicity.

This is an internal construction obtained by composing the published geometric
results and the actual quotient-chart construction. Properness belongs to the
chart scheme's structure morphism; monicity belongs to its natural map into the
parabolic presheaf. The construction supplies one chart for each relative
parabolic over an affine base. It neither asserts that this single chart covers
all parabolics nor constructs the finite union of types or its global descent.
The original smooth proper representability theorem remains a separate target.
