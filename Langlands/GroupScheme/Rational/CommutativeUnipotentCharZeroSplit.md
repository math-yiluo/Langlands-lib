# Commutative unipotent splitness in characteristic zero

This internal construction proves split unipotence over the original field for
every smooth connected affine commutative unipotent group in characteristic
zero. It imposes no algebraic closedness or domination hypothesis on that
field.

The first theorem constructs a nontrivial smooth connected central split
subgroup when the original group is nontrivial. Faithfully flat base change
to an algebraic closure preserves nontriviality. The existing algebraically
closed characteristic-zero classification supplies an actual vector-group
isomorphism of positive dimension. A standard coordinate direction has
nonzero tangent under its inverse.

`PolynomialPoint.finiteGaloisHomModel` descends the inverse's actual polynomial
point and universal additive identity to a finite Galois intermediate field.
Its tangent comparison retains the same nonzero coordinate direction; no
monomorphism of the descended model is assumed. The target is commutative,
so this homomorphism is central. The existing scalar-weighted Galois norm
has nonzero differential for some scalar. Its smooth connected image is a
nontrivial central split subgroup over the ground field.

The second theorem uses induction on the actual Lie dimension. The trivial
group has a split series of length zero. Otherwise, quotient by the constructed
subgroup. The quotient is smooth, connected, affine, commutative and unipotent,
and its Lie dimension is smaller. Induction splits the quotient; the existing
extension construction combines its finite represented additive series with
that of the kernel.

`splitSeriesOfCommutativeCharZero` chooses the resulting length and its actual
represented additive series.

The provenance is internal assembly of the cited Lean imports: algebraically
closed vector classification, finite polynomial coefficient descent, nonzero
norm differential, smooth homomorphism image, and quotient dimension and
series extension. This unit proves the characteristic-zero commutative case;
it does not prove the all-characteristic split-torus domination statement.
