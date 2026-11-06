# Normalized Galois-invariant prolongation over a Henselian valuation ring

Authors: Worker 1651 and Worker 1607 (infinite Galois restriction wrapper).

`henselianRealGaloisProlongation` proves the exact two-universe proposition
`HenselianRealGaloisProlongationStatement`.

For a nontrivial real valuation, choose its proved normalized prolongation
from `RealValuationProlongationExistence`. Restrict it to each finite
Galois intermediate field. The normalization equality follows by
composition of the actual field algebra maps. The finite Henselian
invariance theorem applies to each restriction. Worker 1607's
`valuation_invariant_of_finite_galois` then gives invariance on the
possibly infinite Galois extension: every element lies in a finite
normal subextension, and restriction of any ambient automorphism
commutes with that inclusion.

For a trivial base valuation, take the trivial valuation on the extension
directly. Injectivity of the field algebra map gives exact restriction,
and automorphisms preserve zero and nonzero elements, proving invariance.

The finite invariance argument is implemented in
`HenselianFiniteGaloisInvariant` with its paired descent/separation
helpers: an actual decomposition-subgroup product has an isolated
small conjugate, which Hensel lifting descends to the original field.
The existence argument uses a constructed completion and its algebraic
closure; no completeness of the original field is a hypothesis.

This is a derived proof of the existence-and-invariance consequence of
Kaletha–Prasad Definition 2.1.1 and Proposition 2.1.3, printed p.68/PDF
p.99, and the observation printed p.69/PDF p.100. It does not rely on
the book's unformalized unique-prolongation equivalence. It proves the
requested proposition directly from the actual Henselian valuation ring,
with arbitrary independent universes, no new axioms and no residue,
perfectness, characteristic or finiteness restriction.
