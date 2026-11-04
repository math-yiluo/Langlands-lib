# Semisimple prime-power replacements of actual Lie elements

This internal construction combines finite dimensionality of the actual
Lie kernel with the previously constructed actual prime-power Lie elements
and their simultaneous representation differential formulas. Its provenance
is the algebraic argument implemented below; it invokes no external structural
theorem about algebraic groups or Lie algebras.

For a finite set `s` of natural numbers, coefficients `c : Nat → k`, and
natural numbers `p,m`, `primePowerRelationPolynomial s c p m` is

`sum (i in s), c i * X^(p^(i-m))`.

Here multiplication by `c i` is polynomial scalar multiplication. Suppose
`k` is a field with `CharP k p`, `m` belongs to `s`, and every member of `s`
is at least `m`. Differentiating each summand shows that the derivative is
the constant polynomial `C (c m)`: the summand at `m` has exponent one, and
every other exponent is divisible by `p`. When `c m` is nonzero, an explicit
constant inverse provides a Bezout identity with the derivative, proving
separability. Substitution of `z^(p^m)` in this polynomial gives
`sum (i in s), c i • z^(p^i)` in every possibly noncommutative `k`-algebra
with a ring structure. This uses the exponent identity
`p^m * p^(i-m) = p^i`.

The matrix helper
`isGeometricallySemisimpleMatrix_of_separable_aeval_eq_zero`
shows that any matrix annihilated by a separable ground-field polynomial
is geometrically semisimple in the published sense. The proof maps both
the polynomial and the matrix to the algebraic closure, transports evaluation
through the matrix-to-endomorphism algebra equivalence, and applies Mathlib's
semisimplicity theorem for an endomorphism annihilated by a squarefree
polynomial. Separability survives coefficient extension and implies
squarefreeness there. Thus no perfection assumption on the original field
is used. In particular, a relation
`sum (i in s), c i • M^(p^i) = 0` with the preceding first-coefficient conditions
makes `M^(p^m)` geometrically semisimple.

Finally, `exists_isSemisimpleElement_primePowerKernel` applies to every
actual affine group scheme `G` locally of finite type over a field `k`,
every actual identity-kernel point `X`, and every natural prime `p` with
`CharP k p`. It proves that some `primePowerKernel G X p m` satisfies
`IsSemisimpleElement G`.

The sequence of actual prime-power Lie elements is linearly dependent in
the finite-dimensional actual Lie kernel. Choose a nonzero finitely
supported relation and let `m` be the minimum of its support. Each genuine
finite matrix representation has a linear actual differential. Applying
that differential to the same relation and using the previously proved
prime-power differential formula gives precisely the matrix relation above.
The polynomial argument therefore proves geometric semisimplicity for
every such representation, with the same `m` chosen before the representation.
This is the universal quantifier required by `IsSemisimpleElement`; the
proof does not require a faithful representation or representations of a
base-changed group.

The field and group inhabit an arbitrary common universe. Matrix sizes include
zero. No infinitude, smoothness, connectedness, reducedness, splitness, or
perfection hypothesis is added. This module proves existence of a semisimple
prime-power replacement, but it does not assert that the replacement is
noncentral or nonzero, compare centralizers, establish characteristic-zero
replacement, or prove Cartan generation.
