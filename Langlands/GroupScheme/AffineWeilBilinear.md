# Finite free restriction of bilinear coordinate groups

Let `A` and `B` be commutative rings in an arbitrary common universe `u`, with
an `A`-algebra structure on `B` and a specified basis `b : Basis (Fin n) A B`.
Let `I` be a finite type in the same universe and let `c : I → I → B`.
The bilinear coordinate group over `B` has points `(a, z)` with multiplication
`(a, z)(a', z') = (a + a', z + z' + Σᵢⱼ cᵢⱼ aᵢ a'ⱼ)`.

`functor A B c` is the original affine point functor of that group evaluated on
`B ⊗[A] T` for each test algebra `T`. `affineCoordinates` is a multiplicative
equivalence recovering its tensor-valued bilinear coordinates. Its naturality
uses the actual tensor map induced by every map of test algebras.

`basisCoordinateEquiv` gives set coordinates indexed by
`(I × Fin n) ⊕ Fin n`: basis components of the vector entries, followed by
basis components of the scalar entry. It is a set equivalence, and does not
identify the bilinear group law with the additive law on this coordinate array.
The polynomial algebra on these variables corepresents the same original
group-valued functor (`corepresentableBy`).

`polynomialGroupScheme` recovers the group structure from that functor.
Its relative underlying scheme is the spectrum of this polynomial algebra.
Consequently it is affine, smooth and geometrically connected over `Spec A`.
With the finite and projective module instances required by the existing
affine Weil restriction construction, `restrictionIso` is an isomorphism from
the actual `AffineWeil.groupScheme` to this polynomial model. It is obtained
from natural multiplicative equivalences on every scheme test via group-valued
Yoneda; the test schemes need not be affine or reduced.

For any finite indexing `v : Fin m ≃ I × Fin n`, the vector component functions
are primitive (`vectorPrimitive`). Their `vectorProjection` to the
`m`-dimensional vector group is affine, flat and surjective. These properties
follow from the fact that the vector and scalar variables together freely
generate the polynomial algebra. On every scheme test its kernel consists
exactly of the points whose tensor-valued vector entry vanishes.
`vectorProjectionKernelCoordinates` reads the scalar tensor entry in the
specified basis. These natural multiplicative equivalences establish the
published all-test vector-group predicate in dimension `n` for the actual
scheme-theoretic kernel, over every base ring.

When `A = k` is a field, `polynomial_isUnipotent` applies the published
unipotent-extension theorem to this affine, flat, surjective projection.
Its kernel and quotient are vector groups, so both are unipotent in the
representation-theoretic sense used by the Library. The polynomial model is
also connected because its coordinate algebra over `k` is a domain.
`properties` transports smoothness, connectedness and unipotence through
`restrictionIso` to the actual affine Weil restriction. There is no
separability, reducedness, perfectness or residue-characteristic hypothesis.
The construction also covers empty vector index types and dimension zero.

This is a derived prerequisite for the restriction-of-scalars assembly in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition C.5.1,
printed pp.703–704 / PDF pp.734–735. That passage constructs root models by
restricting the additive, trace-zero and unitary models from the finite
extension's ring of integers. Lemma C.5.3, printed p.705 / PDF p.736, states
the desired special-fibre kernel properties. The explicit polynomial
corepresentation and quotient proof here are internal derived constructions;
they are not assertions that the book states this general bilinear theorem.
This unit does not identify an arbitrary supplied apartment or root-depth
model, or compare its special fibre with this restriction. It does not prove
the full root-depth kernel statement or invoke the host Proposition 8.4.15.
