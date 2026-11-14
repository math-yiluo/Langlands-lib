# Actual kernels commute with affine Weil restriction

This derived construction concerns a finite projective algebra `A → B` of
commutative rings and a homomorphism `f : G → H` of affine group schemes
locally of finite type over `B`. It constructs an isomorphism between the actual
scheme-theoretic kernel of the restricted homomorphism and the actual affine
Weil restriction of the original kernel. All rings lie in arbitrary universe
`u`. No field, reducedness, separability or smoothness hypothesis is imposed.

The construction uses the existing natural `testPointsEquiv` on every scheme
test over `Spec A`, with values on the tensor spectrum of its relative global
sections. The restricted map acts as the original `f` under this equivalence.
`pointwiseKernelEquiv` therefore restricts that multiplicative equivalence to
its pointwise kernels. Composing with `kernelPointsEquiv` on both sides gives
`kernelTestPointsEquiv` for the actual pullback kernels.

Naturality is proved after composing with the original kernel inclusion,
which is a monomorphism. Both sides then reduce to the published naturality of
the tensor-test point equivalence. Yoneda recovery through `isoOfPoints` gives
`kernelIso`. `kernelIso_hom_points` records its action on every test scheme.
The original kernel is affine and locally of finite type because its inclusion
in `G` is a closed immersion, the target `H` being affine and hence separated.
Thus all restrictions in this construction are actual representable group
schemes with their original group laws.

`kernelIso_hom_inclusion` proves the equality of actual homomorphisms
`kernelIso.hom ≫ AffineWeil.map (kernelι f) = kernelι (AffineWeil.map f)`.
Its proof evaluates on every test scheme, uses the restricted map's point
formula, and applies `kernelTestPointsEquiv_inclusion`. Thus the isomorphism
also compares the embeddings of the kernels in the restricted source.

The provenance is the kernel/restriction step used in the proof of
Kaletha–Prasad Lemma C.4.4, printed pp.701–702 / PDF pp.732–733 of the 2023
book, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The source uses the fact that Weil restriction commutes with fibre products.
Here the kernel instance is derived directly from the existing actual tensor
point comparison, actual pullback kernel and Yoneda API. This construction
does not supply a special-fibre/base-change comparison or identify the
unitary integral-family transitions, and does not prove C.4.4 or C.5.3 by
itself.
