# Integral models of finite separable fraction-field extensions

This internal construction implements the integral primitive-element step used
in the proof of Stacks Lemma 37.24.8 (0551), in the registered collection
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0551.html`.
It treats an arbitrary domain R, its specified fraction field K, and a specified
finite separable extension L/K, in independent universes. It does not construct
the finite separable extension that splits geometric components, or the finite
etale neighbourhood required by the full lemma. The nonreduced irreducible-base
case also remains outside this model construction.

Scale a primitive element by a nonzero element of R. Mathlib's localization
integrality theorem makes the scaled element integral over R, and multiplication
by a nonzero element of K preserves the generated intermediate field. The
actual subalgebra R[b] inside L is then a finite R-module and a domain.

Every element of L belongs to K[b]. Clearing a common denominator in this
algebraic expression puts a nonzero R-multiple in R[b]. This proves that L is
the localization of R[b] at the image of the nonzero elements of R. The
localization pushout therefore gives the actual K-algebra isomorphism
`K ⊗[R] R[b] ≃ₐ[K] L`, with the displayed multiplication formula on pure tensors.
The chosen model is constructed from the existence proof; no model existence
or generic comparison is assumed.
