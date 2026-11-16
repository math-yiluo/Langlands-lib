# Actual fibre-zero loci for finite type algebras

This is an internal derived construction for detecting equations in actual
residue-field tensor algebras. It supplies a geometric input for approximation
of fibrewise equations in the central-isogeny argument. No external structural
theorem is asserted. The proof combines the Library's generic flatness,
Chevalley theorem, and noetherian generic-constancy criterion.

For commutative rings `R` and `B` with an `R`-algebra structure and `b : B`,
`fiberZeroLocus b` is the subset of `Spec R` consisting of primes `p` such that
`1 ⊗ b = 0` in `κ(p) ⊗[R] B`. This uses the actual tensor algebra, including its
nilpotents. Neither ring is assumed reduced, and the algebras can inhabit
different universes.

`fiberZeroLocus_baseChange` identifies the locus for the element `1 ⊗ b`
after every ring extension `R → S` with the full inverse image of the original
locus on `Spec S`. This comparison requires neither finite type nor
noetherian hypotheses. The proof first shows that field extensions detect
equations in tensor algebras. Injectivity of the map into a tensor product
over a field gives detection, and the cancellation isomorphism for iterated
base change identifies its value on `1 ⊗ b`. For a prime of `S`, the canonical
residue-field embedding from the contracted prime provides the required
field extension.

`isConstructible_fiberZeroLocus` proves constructibility when `R` is
noetherian and `B` is a finite type `R`-algebra. The proof has the following
steps.

1. `elementAnnihilator b` is the ideal of elements annihilating `b`.
   `annihilatorMul b` is the injective `R`-linear map
   `B/ann(b) → B` given by multiplication by `b`, with cokernel `B/(b)`.
2. Over a domain base, generic flatness of this cokernel makes the injection
   remain injective after every scalar extension inverting one fixed nonzero
   element `a` of `R`. Thus `1 ⊗ b = 0` is equivalent to the tensor algebra
   of `B/ann(b)` being the zero ring on `D(a)`. This equivalence uses
   injectivity on the unit element, so it detects actual zero rather than
   nilpotence.
3. The spectrum fibre equivalence identifies this zero-algebra condition
   with the complement of the image of `Spec(B/ann(b))`. Over a noetherian
   base that image is constructible by Chevalley's theorem. Hence the
   fibre-zero locus intersected with `D(a)` is constructible. Constructible
   membership is constant on some neighbourhood of the generic point of
   the domain base.
4. For each irreducible closed subset `Z` of `Spec R`, its vanishing ideal
   is prime. The quotient by this ideal is a noetherian domain. Apply the
   preceding generic constancy to the base-changed element, and use
   `fiberZeroLocus_baseChange` to transport it to a nonempty relatively
   open part of `Z`. The noetherian generic-constancy criterion then gives
   global constructibility.

The supporting generic exactness statement assumes only that the base is a
domain and the algebra is of finite type; noetherian hypotheses enter when
applying Chevalley and closed-subset induction. Empty spectra are included.
This module does not construct coefficient models or prove global kernel
centrality; those are further uses of this input.
