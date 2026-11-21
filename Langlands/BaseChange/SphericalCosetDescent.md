# Descent of spherical cosets

This module derives the fixed-coset comparison needed by the unit fundamental
lemma. The quotient uses the published spherical subgroup of the actual
general linear group and Mathlib's cosets `xK`, with multiplication by `K` on
the right. The map is coefficient extension. Membership in the spherical
subgroup amounts to integrality of the entries of both a matrix and its inverse.
Reflection of integrality along the field embedding proves injectivity on
cosets. The published action on the extension integers shows that the entrywise
automorphism preserves the extension spherical subgroup, so base-changed cosets
are fixed.

For the other direction, let `σ` generate an unramified cyclic extension of
positive degree `l` and let `xK_E` be fixed. Then `x⁻¹σ(x)` comes from an
integral invertible matrix. Its ordered cyclic norm is one by telescoping in
the field and injectivity of the inclusion of integral matrices. The cyclic
integer action has period `l` and admits a scalar with pairwise unit differences
between its conjugates indexed by `Fin l`. Integral matrix descent therefore
supplies `c` over the extension integers with `x⁻¹σ(x) σ(c) = c`. The matrix
`xc` represents the same coset and is fixed entrywise. Each entry is the image
of an element of the base field, and the determinant of the resulting matrix
is nonzero because its image is the determinant of `xc`. This gives a
representative in the image of the base general linear group.
