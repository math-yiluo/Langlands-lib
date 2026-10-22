# Coinduced coefficients for Tate dimension shifting

Author: Worker 45.

`coinduced A` is Mathlib's actual coinduction of the restriction of `A` to
the trivial subgroup. Its underlying module is identified with functions
from the group to `A`, and the action is right translation of the argument.
The equivariant embedding sends a vector `a` to the function `g ↦ g a`.
Evaluation at the identity splits this embedding as a scalar-linear map.
`coinducedDelta` is the scalar-linear map taking a vector to the function
supported at the identity; it is not claimed to be equivariant.

The norm of a function is the constant function whose value is the sum of
its values. This proves norm surjectivity onto invariant functions and
degree-zero Tate vanishing. Positive-degree vanishing uses Mathlib's
cohomological Shapiro isomorphism. Vanishing in degrees at most minus two
uses its proved finite-index induction/coinduction isomorphism and
homological Shapiro isomorphism. Both reduce to the actual cohomology or
homology of the trivial subgroup.

For degree minus one, write `delta(a)` for the function supported at the
identity. Every function `f` is the sum of the translates
`g⁻¹ · delta(f(g))`. Mathlib's homology differential sends the one-chain
`single g a` to `g⁻¹ · a - a`. Consequently, the boundary of the sum of
`single g (delta(f(g)))` is `f - delta(∑ g, f(g))`. If the norm of `f`
is zero, the second term vanishes. The explicit isomorphism
`minusOneShortComplexIso` identifies this calculation with the actual
Tate complex in degrees minus two, minus one, and zero.
`coinduced_tate_isZero` combines all four degree cases.

The source for induced/coinduced modules and dimension shifting is Serre,
*Local Fields*, Greenberg translation, GTM 67 (1979), Chapter VII, §1,
p. 110 (PDF p. 116), and Chapter VIII, §1, pp. 127–129
(PDF pp. 133–135). Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The implementation uses the pinned Mathlib constructions in `Coinduced`,
`FiniteIndex`, and the two `Shapiro` modules. The use of these established
comparison isomorphisms is an internal formalization choice.

No Tate acyclicity is assumed: every vanishing statement is proved.
