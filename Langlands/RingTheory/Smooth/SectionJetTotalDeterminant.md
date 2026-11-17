# Total augmentation-jet determinant transitions

Let `R` and `A` be commutative rings, with `A` an `R`-algebra and an
augmentation `ε : A →ₐ[R] R`. Put `I = ker ε`. Assume that `A` is formally
smooth over `R`. Let `b` be a specified finite basis of the actual cotangent
module `I/I²`, indexed by `σ`, and let `z` be arbitrary specified lifts of
that basis in `I`. The universes of `R`, `A` and `σ` are independent.

This is an internal assembly of the actual augmentation layers from
`SectionJetLayerDeterminant` using `SplitBasisDeterminant`. It adds no
external source claim.

`JetIndex σ n` is the finite index type for the filtration-adapted basis
of the order-`n` jet. It starts with one scalar index at order zero and
adds the degree-`n+1` homogeneous monomial indices at each next step.
Finiteness is proved by this recursion. The finite enumerations and
decidable equality instances follow the same sum recursion.

`jetExponent σ 0 = 0`, and
`jetExponent σ (n+1) = jetExponent σ n + HomogeneousPolynomial.exponent σ (n+1)`.
`jetExponent_pos` proves positivity for every positive jet order, since
the final layer exponent is positive and the preceding summand is
nonnegative. The homogeneous exponent's documented empty-variable
convention is retained.

`totalBasis z b hz hzb s hs n` is a basis of the actual quotient
`A/I^(n+1)`. Here `s` is any supplied family of `R`-linear right inverses
to the actual quotient truncations. At order zero the basis is the scalar
basis transported through the actual zero-jet augmentation equivalence.
At each next step it is the adapted product of the preceding jet basis
and the actual homogeneous layer basis, using the supplied section.

`totalBasis_toMatrix_det` compares two such total bases with arbitrary
cotangent bases and lifts, and with two independently supplied families
of linear sections. It proves that the actual basis-transition
determinant equals

`det(b.toMatrix b') ^ jetExponent σ n`.

The implemented proof is induction on the jet order. At order zero the
two scalar bases agree. The next adapted-basis transition determinant
is the product of the lower-jet and actual layer transition determinants
by `SplitBasis.adaptedBasis_toMatrix_det`, which permits different
sections on both sides. The induction hypothesis and the actual layer
power formula combine by addition of exponents. This explicitly proves
independence of the truncation-splitting choices at the determinant level.

Finally, `chosenTotalBasis` supplies the sections using the already
constructed projective quotient splittings when `A` is also of finite
type over `R`. This extra hypothesis belongs only to that choice
construction; the comparison theorem is formulated for supplied
sections and does not require finite type. No field, domain or
noetherian assumption is made. This module compares bases indexed by
the same finite cotangent type and does not yet construct a sheaf
determinant-line isomorphism or the actual group Lie comparison.
