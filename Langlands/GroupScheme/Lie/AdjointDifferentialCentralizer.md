# The actual adjoint differential and tangent centralizers

This internal derived module uses finite natural coordinates on the actual
Lie kernel of an affine group scheme. `adjointDifferentialFamily` is the
linear differential of its constructed algebraic adjoint representation,
converted from matrices to endomorphisms of the coordinate module.

The first-order matrix `1 + epsilon M` fixes the constant vector associated
to `v` exactly when `M v = 0`: the epsilon coefficient of its action is
`M v`. Applying this calculation to the actual adjoint representation and
using coordinate naturality identifies membership of `Y` in the actual
all-test tangent centralizer of `X` with the vanishing of the adjoint
differential of `Y` at the coordinates of `X`.

Over a field and for an affine locally finite-type group, the independently
proved symmetry of actual tangent-centralizer membership reverses `X` and
`Y`. Consequently the tangent centralizer of `X` is the kernel of its own
adjoint differential, in these coordinates. Coordinate surjectivity proves
that it is the full Lie module exactly when that endomorphism is zero.

If `X` is representation-semisimple and its tangent centralizer is proper,
the adjoint differential is nonnilpotent over the original field. A
hypothetically nilpotent differential gives a nilpotent tangent matrix;
after extension to the algebraic closure that endomorphism is also
semisimple by the actual representation test. It is therefore zero.
Faithfulness of field extension makes the original matrix zero, contradicting
the full-centralizer criterion. This allows arbitrary characteristic,
imperfect fields, and dimension zero.

The provenance is this derivation from the actual adjoint representation,
its dual-number differential, coordinate naturality, tangent-centralizer
symmetry and Mathlib's semisimple nilpotent endomorphism criterion. No
external structural assertion is assumed. Scalar-extension comparison with
the adjoint family, semisimple replacement and Cartan generation are not
proved here.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
