# Invariant positive forms under conjugate-linear equivariant maps

This derived construction transports the published `InvariantPositiveForm`
along actual equivariant conjugate-linear maps. It is a prerequisite for using
a Hermitian identification with a smooth dual. It does not construct that
identification or prove smooth-dual unitarizability.

The acting object is an arbitrary monoid. The complex module carriers and the
monoid have independent universes; neither carrier needs a norm, topology,
completeness or finite dimension.

For an injective conjugate-linear map `f : V →ₗ⋆[ℂ] W` intertwining `ρ` and `σ`,
and a positive invariant form `b` on `σ`,
`InvariantPositiveForm.conjugateComap` defines

`b'(v,w) = b(f(w),f(v))`.

The order of the arguments is essential: the published form is conjugate-linear
in its first argument and linear in its second. Conjugate linearity of `f`
and reversal of the arguments give the same convention for `b'`. The
construction uses Mathlib's right-additivity and right-scalar identities for
the inner-product core. Hermitian symmetry and nonnegativity follow directly
from `b`; injectivity makes the pulled-back form definite. Equivariance and
invariance of `b` prove invariance of `b'`. The evaluation identity is
definitional.

`IsUnitarizable.of_conjugate_injective` transports existence of a form.
`isUnitarizable_iff_of_conjugateEquiv` applies this construction to a
conjugate-linear equivalence and its inverse. Equivariance of the inverse
follows by injectivity of the original equivalence.

The provenance is internal: this is an elementary transport of the published
positive-form structure, paralleling its linear `comap` constructor while
accounting for conjugation. No literature theorem, classification assertion,
ordinary linear self-duality, or infinite-dimensional Riesz theorem is used.
