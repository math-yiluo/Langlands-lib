# Arithmetic polynomial systems for the cuspidal Harris reduction

Author: Worker 773.

`HarrisPowerSystem` is a derived predicate on a given collection of actual
continuous representations over the completions of one number field. It
records a positive integer `a`, dimension `a(r+1)`, and one finite exceptional
set of field places. At every good place, `P` is monic of degree `r+1`, has
nonzero constant coefficient, and is pure of weight `r` at every complex
embedding. The representation at every included coefficient place of
different residue characteristic is unramified there with Euler polynomial
the image of `(P^a).reverse`.

At the chosen complex embedding, `P.reverse` equals the arithmetic Euler
polynomial of an actual spherical spectral system of the cuspidal class at
each good place. The normalization is `clozelEulerPolynomial` at residue degree
one. If `q` is the residue cardinality and `α_i` are the unramified eigenvalues,
the factors are `1 - q^(r/2) α_i X`. `HarrisNormalizedSystem` is this
predicate with `a = 1`.

## Provenance

This interface isolates the common polynomials used in both multiplicity
removal and quadratic base change. Clozel's trace identity for all Frobenius
powers gives the power convention. The CM theorem works over Clozel's reflex
field. Specialization to an actual identification with the cuspidal base
field, coefficient rationality of the monic root and purity are obligations
for the route that supplies this predicate. During quadratic base change the
arithmetic roots are raised to the residue degree, using `q_w = q_v^f`.

- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991), §5.1,
  equations (5.2)–(5.3) and Theorem 5.3, pp. 131–132, and Theorem 5.7, p. 142.
  Registered `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), Definition 1.1, pp. 183–184,
  Theorem 1.2, p. 185, and unramified base change in Definition 1.3, p. 186.
  Registered `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

These definitions provide the polynomial interfaces. Existence and the
passage to the sum-of-pure-families conclusion of Harris's theorem are
separate statements.
