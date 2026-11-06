# Finite neighborhoods separating CM conjugation ratios

Author: Worker 1692.

This internal helper develops the finite-neighborhood step needed for the
weight-one character construction of Harris–Taylor, proof of Corollary VII.2.8,
printed pp.244–245 (PDF pp.252–253). The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source reduces to compatibility on global units; this module derives a
version for arbitrary principal factors that can occur in the idele quotient.

For a CM number field `K`, `conjugationRatio a` is `a / c(a)` in `Kˣ`, and
`ideleConjugationRatio` is the continuous homomorphism `x ↦ x / c(x)` on the
actual idele group. `finiteIdeleProjection K w` is reused from `Langlands.Global.Adelic`
with its existing coordinate formula and continuity.

If the principal idele of `a / c(a)` is integral at every finite place, the
principal-idele unit criterion writes it as a unit of the ring of integers.
Its absolute value at every infinite place is one, so Mathlib's unit torsion
criterion puts it in the finite group of global roots of unity.
This is `exists_torsion_of_integral_conjugationRatio`.

`exists_openSubgroup_separating_torsion w` gives an open subgroup of `K_wˣ`
whose intersection with the global roots of unity is trivial. The embedding
of the ring of integers in the completion is injective. Its finite torsion
image, with the identity removed, is closed and misses the identity.
Van Dantzig's theorem supplies an open subgroup in its complement. The local
field realization provides local compactness and total disconnectedness in
the existing completion topology.

`exists_open_integral_subgroup_forcing_real S` constructs an open subgroup
`H` of the actual ideles. It is contained in the integral ideles and contains
every infinity idele. Suppose `a : Kˣ`, `b` is an idele fixed by the CM
involution, and `s` is an integral idele whose finite coordinates outside `S`
are one. If `diagonalUnits K a * b * s` lies in `H`, then `c(a) = a`.
No disjointness condition on `S` is needed for this conclusion.

Choose a finite place `w` outside `S` and its conjugate; the infinitude of
finite places ensures this choice. Intersect the open integral ideles with
the inverse image, under the `w` coordinate of `x / c(x)`, of an open subgroup
separating the global roots of unity. Taking conjugation ratios cancels `b`.
The integrality assumptions make the principal ratio integral; hence it is
a global root of unity. The factor `s / c(s)` has coordinate one at `w`,
so the separating condition forces that root of unity to be one.

The module does not yet assert local norm compatibility or the existence of
a Hecke character. Those require the subsequent norm/sign and quotient steps.
