# A uniform generator bound for finite coefficient fibers

This derived construction supplies a quantitative finite-fiber input for
the finite locally free Weil model in Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), Example 4.2, printed pages 9–10.
It is auxiliary algebra, not an assertion quoted verbatim from that
example. The coefficient algebra here is only required to be finite as a
module; projectivity and a separability hypothesis are unnecessary.

For a commutative A-algebra B with `Module.Finite A B`,
`finiteAlgebraFiberBound A B` chooses the size of a finite generating
family using Mathlib's `Module.Finite.exists_fin'`.
`finiteAlgebraFiberBound_surjection` retains the actual surjective A-linear
map from that many copies of A to B. The bound depends on this original
finite algebra, rather than on a field fiber.

For every field C with its specified A-algebra structure,
`finiteAlgebraFiberBound_finrank` bounds the dimension of the original
tensor algebra C tensor_A B by that same natural number. The proof base
changes the chosen surjection, reuses Mathlib's base-change surjectivity,
and compares dimensions. Mathlib's scalar finite-product tensor
equivalence identifies the source with the prescribed number of copies
of C.

`finiteAlgebraFiberBound_card` bounds the number of original prime ideals
of C tensor_A B by the same number. The private cardinal comparison first
uses that a finite-dimensional algebra over a field is Artinian. It then
reuses `IsArtinianRing.finrank_eq_sum_primeSpectrum`, which expresses its
dimension as the sum of the dimensions of the original localizations at
its prime ideals. Each localization is nonzero and finite-dimensional;
finiteness follows from Mathlib's surjectivity of localization for an
Artinian ring. Hence every prime contributes at least one to the sum.
The spectrum is finite by the existing Artinian instance. This proves
the cardinal inequality, including the zero algebra with empty spectrum.

All rings inhabit one arbitrary universe. No domain, Noetherian, reduced,
separable, projective or topological hypothesis is imposed on A or B.
In particular, the tensor fibers may have nilpotents. The bound concerns
all original primes of every original field tensor algebra, not just
rational or separable points. Its comparison to scheme-theoretic fibers
of the universal finite base change and the actual Weil model's finite
affine cover remain subsequent host obligations.
