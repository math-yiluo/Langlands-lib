# Descending an isolated small conjugate over a Henselian valuation ring

Author: Worker 1651.

If an algebraic element b in a Galois extension has
value less than one and each other root of its minimal polynomial has
value one, its minimal polynomial is integral and has a simple residue
root at zero. Indeed its derivative at b is the product of b minus every
other root, all of value one. Integral polynomials and their derivatives
are one-Lipschitz on integral elements, so the derivative remains a unit
at zero while the polynomial value at zero is small. Hensel lifting over
the original field gives a root c congruent to zero. Uniqueness of the
simple root near b implies b is the image of c. All normalization maps
are the actual field algebra map.

This derived internal lemma is the minimal-polynomial descent step
used by `HenselianFiniteGaloisInvariant`. It uses the published generic
valuation Hensel and Lipschitz lemmas in `SeparableInertiaNormAmbient`
and `SeparableInertiaNormReduction`, together with Mathlib’s actual
minimal polynomial, roots, separability and derivative product formula.
The base and Galois ambient field have independent arbitrary universes.
The Galois extension may be infinite in this particular descent lemma;
only the minimal polynomial and its finite root multiset enter the proof.
It retains the original Henselian valuation subring and the exact
pullback equality of real valuations.
