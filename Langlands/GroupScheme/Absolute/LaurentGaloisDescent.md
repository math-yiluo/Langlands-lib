# Descent of Galois-invariant Laurent coordinates

Worker 1272.

This is an internal algebraic construction for the descent step following
the cocharacter orbit sum in Milne, *Algebraic Groups* (2017), Theorem 25.1,
printed page 544 (PDF page 560). It supplies a coordinate argument using
Mathlib's finite Galois fixed-field theorem.

For a finite Galois extension `K / k`, `extend` applies the field inclusion
to every coefficient of a Laurent polynomial. It is injective.
`conjugate` similarly applies an algebra automorphism of `K` to every
coefficient. A Laurent polynomial belongs to the image of `extend` if
and only if every such automorphism fixes it: equality of coefficients
reduces the assertion to the fixed-field theorem, and the finite-support
description of the coefficient map assembles the preimages.

`descendRingHom` constructs the unique ring map into the Laurent
polynomials over `k` whose extension is a given invariant Laurent-valued
ring map. The ring laws follow by applying the injective extension map.
`descendAlgHom` retains the algebra structure when the original map is a
map of algebras over `k`.

This file supplies the algebraic coordinate construction. Identifying
these coordinates with the published Galois action on cocharacters and
proving that the descended scheme map is a group homomorphism remain
separate steps. It does not yet assert cocharacter descent.
