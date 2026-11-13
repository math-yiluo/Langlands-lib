# The diagonal μ₂ in the combined binary spin lift

This internal construction defines the image of the original diagonal μ₂ under
the combined binary spin homomorphism. It identifies its image functor with the
intersection of the combined image and the supplied spin kernel, on every
relative test scheme, and gives a precise criterion for the combined lift's
kernel.

First, `FirstKindInvolution.IsSpinCover.kernel_isCentral` proves that the full
scheme-theoretic kernel of a supplied quaternionic spin cover is central. Its
assumptions are a field `K`, a finite-dimensional division `K`-algebra `D`, a
first-kind involution `σ`, a quadratic form `q` on a finite index type, and
`π : S ⟶ σ.isometryGroup q` satisfying `σ.IsSpinCover q π`. The proof uses the
central isogeny to the isometry identity component supplied by this predicate.
Monomorphy of the identity-component inclusion makes the two kernel conditions
equivalent on every test.

The remaining constructions are in `BinarySpinLift`. Here `K` is infinite,
`D` is central of dimension four, the symmetric subspace of `σ` has dimension
three, and `h : σ.IsHyperbolicPair q e f` is supplied. Constructions involving
the combined spin lift retain the explicit premise
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`.

The theorem `existsUnique_diagonal_of_ambient_eq_one` gives a unique original
μ₂ point over every test scheme for each point in the kernel of
`AmbientBinaryScheme.isometryHom`. It is the pointwise consequence of the
existing full ambient-kernel representation and the monomorphism
`BinaryKernel.diagonal`. This theorem itself needs no spin-cover or
simple-connectedness premise.

The morphism `diagonalSpin` is
`BinaryKernel.diagonal hdim ≫ BinarySpinLift.productHom ...`. The theorem
`diagonalSpin_comp` says that its composite with the supplied `π`, on underlying
schemes, is the constant identity morphism. The proof uses the combined
homomorphism's ambient composite and the full ambient-kernel representation.
Consequently `diagonalSpin_isCentral` follows from centrality of the supplied
spin kernel, on all relative tests.

The equality `diagonalSpin_range` is

`range diagonalSpin = range productHom ⊓ range (kernelι π)`.

These ranges and their intersection are the actual subgroup functors of
relative test points. For the reverse inclusion, a combined-image point in
the spin kernel comes from a product point in the ambient kernel. The unique
diagonal preimage of that product point gives the required original μ₂
preimage. No extension of the test scheme is used.

The criterion `productHom_eq_one_iff_diagonal` says that a product point is in
the kernel of the combined spin lift exactly when it is the image of an
original μ₂ point whose `diagonalSpin` image is the identity. Finally,
`productHom_points_injective_of_diagonalSpin` shows that monomorphy of
`diagonalSpin` implies injectivity of `productHom` on every test. The proof
applies the kernel criterion to the quotient of two product points with the
same spin image, and then cancels the assumed diagonal monomorphism.

The provenance is internal: the construction uses the supplied central
isogeny, actual ambient μ₂ kernel, combined lift's ambient composite, and
relative point-group laws. It permits arbitrary characteristic and nonreduced
test schemes. Monomorphy of `diagonalSpin` and coverage of the full supplied
spin kernel remain separate obligations.
