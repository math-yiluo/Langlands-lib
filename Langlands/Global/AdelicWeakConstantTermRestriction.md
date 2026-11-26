# Exponent comparison for nested constant terms

For a polynomial orbit of the positive split component, a raw left shift in that component
preserves the exponent. Commutativity lets the shift enter the base point of the orbit.
Scalar multiplication and subtraction preserve the same polynomial orbit condition. Thus in a
finite exponent expansion, a power of a shift minus a scalar preserves each exponent space.
If that power kills the sum, directness implies that it kills every component. On each
nonzero component the generalized eigenspace for the raw exponent value and the generalized
eigenspace for the given scalar intersect nontrivially, so the two values agree. This is
`exponent_value_eq_of_shift_sub_pow_sum_eq_zero`.

For `Q ≤ P`, `exponent_value_eq_of_constantTerm` applies this to the constant term along `Q`
of a function with one normalized `P`-exponent. The function is left invariant under the
radical of `P` and its `Q` constant term is absolutely integrable. The product-of-differences
identity in `AdelicConstantTermSplitComponent` transports the annihilating power across the
constant term. At matching positive points the shift is the same actual adelic left shift,
so every nonzero `Q` component has the given raw `P`-exponent value there.

`unitaryExponentSum_constantTerm_eq_zero_of_nonunitary` uses equality of the two half moduli
at matching positive points. Canceling this common nonzero factor gives equality of the
normalized exponent values. If a unitary `Q` exponent had a nonzero component, its value at
all lifts from the positive component of `P` would have absolute value one. The real
character logarithm of the positive component is surjective, so the real part of the
`P` exponent would vanish. This contradicts its nonunitarity, and the unitary sum is zero.

Source. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See Lemma 3.8 (iii), p.14.
