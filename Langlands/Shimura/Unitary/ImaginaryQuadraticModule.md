# Actual imaginary quadratic module decomposition

This internal construction uses the actual algebra splitting and idempotents
from `ImaginaryQuadraticTensor` and `ImaginaryQuadraticProjectors`. Let `L` be an
imaginary quadratic CM number field, `K` a characteristic-zero field containing
it, and `R` any commutative `K`-algebra with compatible rational scalars. The
module `M` has an `R`-module structure and a compatible rational module
structure. Its input action is an actual unital ring homomorphism from `L`
to the `R`-linear endomorphisms of `M`.

`tensorAction` extends this action to an `R`-algebra homomorphism
`R ⊗[ℚ] L → End_R(M)` using the tensor universal property. On `r ⊗ t` its
endomorphism is `r` times the given endomorphism for `t`. Rational compatibility
of the input ring homomorphism is automatic for rational algebras.

`eigenmodule` consists of exactly those vectors satisfying all equations
`rho(t)m = character(t)m`, for the natural character when the Boolean is `false`
and the conjugate character when it is `true`. Additivity and `R`-linearity
prove these subsets are actual `R`-submodules.

`moduleProjector` is the image of the corresponding actual coordinate
idempotent under `tensorAction`. Transport of the idempotent equations proves
that these endomorphisms are idempotent, orthogonal, and sum to the identity.
The character identity for multiplication on a coordinate idempotent proves
that every projected vector satisfies the corresponding eigencondition.

Conversely, tensor induction proves that on an eigenvector the whole tensor
algebra acts by its corresponding scalar evaluation. Evaluating at the two
idempotents proves that the vector is fixed by its own projector and killed
by the other one. Thus the image submodule of each projector is exactly the
simultaneous eigensubmodule.

`eigenmoduleEquiv` is the resulting actual `R`-linear equivalence from `M` to
the product of these two eigensubmodules. Its forward map is the pair of
constructed projectors; its inverse adds the two included vectors. The sum,
fixed-vector and zero-vector identities prove the two inverse laws. No
finiteness, reducedness or nontriviality assumption on `R` or `M` is required.

This derived algebraic unit assumes no output projector or decomposition.
It does not yet compare the eigensubmodules with scalar-extension tensor
factors, construct a Lie-sheaf decomposition, assert ranks or prove a
geometric compatibility equivalence.
