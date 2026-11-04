# Semisimplicity through actual representation subquotients

This derived internal module supplies the linear algebra needed for reflecting
`Lie.IsSemisimpleElement` along a group scheme homomorphism. Semisimplicity passes
back through injective intertwiners and forward through surjective intertwiners:
the proof regards the intertwiner as a polynomial-module homomorphism and uses
Mathlib's submodule and quotient preservation of semisimple modules. For matrices
over a field, linear splittings show that injection and surjection persist after
any commutative scalar extension. Applying this over the algebraic closure gives
the corresponding geometric semisimplicity transfer, including dimension zero.

`MatrixRepresentation.Intertwines ρ σ C` requires equivariance of the constant
matrix `C` on every affine algebra test of the actual group scheme. This includes
dual numbers, so extracting their epsilon coefficient proves that the same
matrix intertwines the actual tangent matrices. No rational-point density is
used.

`MatrixRepresentation.IsSubquotientOf σ ρ` means there is an intermediate finite
dimensional actual group scheme representation, an injective intertwiner into
`ρ`, and a surjective intertwiner onto `σ`. Its differential inherits geometric
semisimplicity from the differential of `ρ`. Consequently, if every representation
of the source is such a subquotient of a restricted target representation,
representation-tested semisimplicity reflects along the group scheme map.

These are internal compositions of the published actual matrix representation
and dual-number differential interfaces with Mathlib's polynomial-module and
semisimple-module constructions. The module does not construct ambient
representations for a closed subgroup or assert that its subquotient premise is
automatically available. It imposes no smoothness, connectedness, infinitude,
perfection, characteristic, or splitting condition.
