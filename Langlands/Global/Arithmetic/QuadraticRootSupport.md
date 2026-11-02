# Square-root intermediate fields

Worker 27 authored this internal algebraic support module for the auxiliary
quadratic construction. `Langlands.Global.rationalRootField x` is the actual
intermediate field `ℚ⟮x⟯` of the supplied ambient field. The definition imposes
no square equation or degree condition; those appear in the following lemmas.
All ambient universe levels remain arbitrary.

For fields `F` and `E` with the supplied `F`-algebra structure, a root
`x ^ 2 = algebraMap F E a` is integral, using the monic polynomial
`X ^ 2 - C a`. If `a` is a nonsquare in `F`, Mathlib's prime-exponent Kummer
polynomial criterion proves this polynomial irreducible. The minimal-polynomial
uniqueness theorem identifies `minpoly F x`, and the simple-extension dimension
formula gives `Module.finrank F F⟮x⟯ = 2`. These lemmas use independent
universes for `F` and `E`.

For a rational `d` and a root in an arbitrary characteristic-zero ambient
field, `rationalRootField_gen_sq` proves the same equation for the actual
subtype generator. Integrality makes the rational root field finite over
`ℚ`, and `rationalRootField_numberField` supplies its `NumberField` instance;
this does not require nonsquareness.

For positive `d`, the complex equation `z ^ 2 = d` implies that `z.im = 0`:
the real part of the square and positivity force `z.re` to be nonzero, while
the imaginary part is `2 * z.re * z.im = 0`. For every complex embedding of
the root field this applies to the generator. The embedding and its complex
conjugate agree there, so the simple-adjoin homomorphism extensionality theorem
makes them equal. This proves `rationalRootField_totallyReal`. For negative
`d`, any real embedding would send the generator to a real number whose square
is negative. This contradiction proves `rationalRootField_totallyComplex`.
The two signature statements impose the respective strict sign but no
nonsquareness premise.

Finally, `rationalRootField_two_embeddings` assumes `d` is a rational
nonsquare and becomes a square in another characteristic-zero field `L`.
Choose a root `y` in `L`. The power basis of the simple extension lifts the
roots `y` and `-y` of its identified minimal polynomial to rational algebra
homomorphisms. Equal homomorphisms would agree on the generator, giving
`y = -y`, hence `y = 0` and `d = 0`, contradicting rational nonsquareness.
The two resulting homomorphisms are therefore distinct. In particular this
applies to `L = Padic p`, including `p = 2`, with no local-prime or completion
claims made by this module.

The provenance is internal, derived algebraic infrastructure motivated by Guy
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Inventiones Mathematicae 139 (2000), Section 3.3, printed page
449, second paragraph (PDF page 11). Worker 27 read that page of the registered
original `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The paragraph chooses imaginary and real quadratic fields split at `p` and
disjoint from a given field; it does not state the generic support lemmas
implemented here. This module proves only the algebraic assertions described
above. Rational square-class supply, actual split primes, topological
completion comparisons, the common-algebraic-closure choices and the required
compositum disjointness remain separate obligations.
