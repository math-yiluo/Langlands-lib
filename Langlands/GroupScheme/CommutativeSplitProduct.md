# Actual products from split commutative group-scheme homomorphisms

Author: Worker 1561.

This internal, derived construction supplies the actual product isomorphism used
when a homomorphic retraction has been constructed. Let `E` be a commutative group
scheme over any scheme `S`, and let `q : E ⟶ V` and `s : V ⟶ E` satisfy
`s ≫ q = id`. The construction imposes no finiteness or geometric conditions on
these groups. It does not prove the existence of such a section or retraction.

`complement q` is the full scheme-theoretic kernel of `q`, with the commutative
group law inherited from `E`. On every relative scheme test, `pointsEquiv` sends
a pair consisting of a kernel point and a point of `V` to the product of their
images under the kernel inclusion and `s`. The existing
`RelativeRoot.CommutativeVectorSplitExtension.splitPointEquiv` proves that this
is a multiplicative equivalence. The product point equivalence and that splitting
equivalence are both natural under every relative scheme morphism.

The pointwise Yoneda construction `isoOfPoints` therefore gives the actual
group-scheme isomorphism `iso : kernel q ⊗ V ≅ E`. The theorem `iso_hom_points`
recovers the multiplication formula on every relative scheme test.
`factorIso : E ≅ V ⊗ (complement q).toGrp` uses its inverse and the categorical
symmetry to put the section factor first.

Over the spectrum of a noetherian ring, `complement_geometry` proves that this
same complement is smooth, affine, and connected if `E` has these properties and
`V` is separated. It applies the existing
`SplitKernelRetract.smooth_connected_kernel` to the identity factorization of
`q`. Affineness follows from the closed kernel inclusion and the affineness of
`E`. These conclusions apply to the actual scheme-theoretic kernel, including
its behavior on nonreduced tests.

The proofs are formal consequences of the cited Library constructions. This
module has no additional external mathematical input. It supports the existence
assertion of CGP, *Pseudo-reductive Groups*, second edition (2015), Theorem
B.2.5, but does not establish the vector factor, the splitting maps, unipotence,
or affine-line constancy required for that theorem.
