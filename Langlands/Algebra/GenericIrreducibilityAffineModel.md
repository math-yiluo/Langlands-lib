# Specializing a hypersurface model in the actual field fibre

Worker 336. This internal supporting module combines the hypersurface model
with the tensor injection and containment lemmas. It is a derived algebraic
argument for the affine geometric irreducibility spreading proof.

Let R be a domain and C a commutative R-algebra. Suppose a model consists of
algebraically independent coordinates z, an additional element w satisfying
a monic relation F, a polynomial g, a fixed exponential-characteristic power,
and integral dependence after multiplication by powers of a base element r.
For a field R-algebra K, assume r stays nonzero and the specialized relation
F is irreducible. If the image of g avoids every minimal prime of the actual
tensor K tensor_R C, this tensor has prime nilradical.

The implemented proof realizes the hypersurface as `AdjoinRoot` of the
specialized polynomial. It is a domain because the polynomial is prime in
the unique factorization domain K[z][X]. Polynomial evaluation into the
actual tensor is injective by the localization lemma. Integral ideal
contraction then makes the hypersurface evaluation injective. The image
contains R[z,w], and the uniform power containment extends by tensor
induction. The existing `nilradical_isPrime_of_radicial` lemma applies.

This module reuses the radicial lemma from the published Anthropic FLT proof
of `Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime`, retaining
its existing attribution and import. The specialization argument here uses
integral contraction in place of its dimension argument, allowing arbitrary
field maps without a finite type hypothesis over a ground field.
The first helper retains minimal-prime avoidance as an explicit input; the
domain spreading core below supplies it uniformly after shrinking.


The module also proves the domain spreading core under the explicit fraction-field
separable-closure premise of the hypersurface model. Flattening the polynomial
via `optionEquivLeft` allows the published absolute polynomial irreducibility
spreading theorem (Stacks 0557) to choose a nonzero base element. Worker 1606's
`GenericDensity.exists_ne_zero_tensor_mul_injective` supplies another base
element making the image of g a non-zero-divisor in every tested field tensor.
A non-zero-divisor avoids all minimal primes. Combining these elements with the
integrality denominator gives a single nonzero element and the tensor prime
nilradical conclusion for all field maps. The companion generic-fibre comparison derives the separable-closure
premise from geometric irreducibility of the generic tensor.
Worker 1606 authored the reused density module; Worker 336 authored this assembly.
