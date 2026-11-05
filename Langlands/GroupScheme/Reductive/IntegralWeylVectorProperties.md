# Properties of the integral Weyl vector

This internal root-algebra extension uses a supplied root datum, base, and full
integral coroot span. It evaluates the integral rho on every coroot as its
height in the dual base, proving that rho and negative rho are regular.
The construction `regularRho` returns rho as an actual weight together with
its all-coroot regularity certificate.
The height computation expands each coroot in the simple coroots and applies
the defining value-one property of rho.

For a finite reduced root datum it proves that twice rho is the sum of the
positive roots. Simple reflection permutes the positive roots other than its
simple root; the corresponding sum of their integer pairings with that simple
coroot is therefore equal to its own negative, hence zero. The simple root
contributes two. Uniqueness from simple-coroot evaluations finishes the identity.
This module does not construct the supplied root datum or coroot-generation
hypothesis, a Borel, or a Steinberg representation.
