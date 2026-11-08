# Actual upper points and contraction for the weighted Hermitian scheme

This internal unit uses the actual weighted Hermitian group scheme and its split
diagonal cocharacter. For a separable quadratic extension `L/k`, a finite middle
index in `Type`, a conjugation-fixed diagonal form `H` and unit middle weights,
it constructs the upper-root subgroup functor on all relative test schemes.
The fields have arbitrary common universe and arbitrary characteristic. No
anisotropy is required.

`upperSpecialUnitaryHom` restricts the existing coupled upper matrix embedding
to the actual full-form special-unitary subgroup. The coefficient compatibility
of that embedding proves `specialUnitaryMap_upper`. Transport through the
all-test matrix equivalence defines `upperPoints`; its naturality makes its
range a subgroup functor `upperFunctor`.

The existing parameter scaling multiplies the middle vector by a
conjugation-fixed scalar `t` and the upper-right scalar by `t²`.
`Parameters.scale_map` proves compatibility with coefficient changes, directly
on both coordinates. Applied to the actual affine-line coordinate and the
pulled-back original parameter, this defines a scheme morphism
`upperContraction`. Its restriction formula follows from parameter naturality,
coefficient composition and scalar inclusion.

The established diagonal conjugation formula for the actual general-linear
embedding proves that the curve restricts to the conjugation orbit under the
actual split cocharacter. At zero both coordinates vanish, so the curve has
identity value there. These two facts give
`upperFunctor_le_dynamicUnipotent`, an inclusion of actual subgroup functors.

The provenance is internal: the construction follows the implemented SU3
polynomial-contraction method, using the previously proved arbitrary finite
weighted middle form, its parameter scaling, actual isometry scheme and
cocharacter. The inclusion proved here does not assert equality with the
dynamic unipotent subgroup, identify a parabolic radical, or establish general
local Kneser–Tits.
