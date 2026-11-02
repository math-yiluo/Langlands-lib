# Factorization through actual isogenies

This internal construction generalizes the effective-epimorphism argument in
`Langlands.AbelianScheme.IsogenyInverse`. It uses the same actual group-scheme
kernel and the same finite, flat, surjective isogeny predicate.

For group schemes `G,H,J` over an arbitrary scheme `S`, with `J` commutative,
let `f : G ⟶ H` be an
isogeny and `g : G ⟶ J` a homomorphism whose composite with the scheme-kernel
inclusion of `f` is the trivial homomorphism. The construction produces an actual
homomorphism `H ⟶ J` with composite `g`, and proves its uniqueness.

The proof first divides two points having the same image under `f`. Their
quotient factors through the actual scheme kernel, so `g` kills it. This proves
equality after applying `g` on all test schemes. Effective epimorphism descent
constructs the scheme map. Cancellation along `f` proves that it is over `S`;
cancellation along `f × f` proves preservation of multiplication. Preservation
of the unit follows from the unit equations for `f` and `g`.

No characteristic, noetherianity or projectivity hypothesis is needed for this
factorization. This is a universal-property construction for a
supplied isogeny; it does not construct an integral model of a rational action or
prove CM moduli representability.
