# Lifting residue automorphisms of finite étale local algebras

Let `O` be a commutative local ring and `C` a finite étale Henselian local
`O`-algebra with faithful scalar action and a local structure map.
`liftResidueAut` lifts an automorphism of the residue field of `C` over
the residue field of `O` to an `O`-algebra automorphism of `C`.
Its reduction at every element is the specified residue automorphism.

Mathlib supplies an algebra generator `x` of `C`, the presentation by its
monic minimal polynomial, and the identification of the reduction of
that polynomial with the minimal polynomial of the residue of `x`.
The residue automorphism carries the residue of `x` to another simple
root. Hensel lifting produces an integral root with that residue, and the
presentation gives the endomorphism sending `x` to this root. The new
root generates because its residue generates. Thus the endomorphism is
surjective, and a surjective endomorphism of a finite module over a
commutative ring is injective. Agreement on the generator proves the
residue formula.

This internal construction supplies the residue-automorphism lift for
the embedded unramified integer order in the division-unit conjugation
appearing in Drinfel'd, *Coverings of p-adic symmetric regions* (1976),
§2 A, printed p. 109.
