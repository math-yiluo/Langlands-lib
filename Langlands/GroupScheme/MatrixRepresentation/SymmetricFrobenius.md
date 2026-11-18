# The actual stable Frobenius subspace of a symmetric power

Let `k` be a field of characteristic exponent `p`, and let `rho` be an
actual finite matrix representation of any group scheme over `Spec k`.
The matrix `SymmetricFrobenius.inclusion k p` has as its columns the
monomial-coordinate vectors of the polynomials `X j ^ p`. Its range,
`symmetricFrobeniusSubspace k n p`, is the pure-power span in the finite
symmetric coordinates. No geometric assumption on the group is needed.

The coefficient formula commutes with every ring map. For positive `p`,
evaluating an included vector at the distinct pure-power monomial indices
recovers its original coordinates; `inclusion_injective` proves injectivity
even over arbitrary commutative rings. The range definition itself does not
require this positivity assumption.

Over every `k`-algebra `A`, linear substitution on `X j ^ p` is the sum of
`(M i j)^p * X i ^ p`. The proof uses the existing characteristic-power ring
map for algebras, which handles the zero algebra as well as nonreduced ones.
Taking coefficients gives
`symmetricMatrix(M) * inclusion = inclusion * entrywisePower(M)`.
For characteristic zero the characteristic exponent is one and this is
just the linear-degree action; the intended Nagata application uses a
positive prime characteristic.

`frobeniusPower_intertwines_symmetricPower` identifies this equation with an
actual intertwiner from `rho.frobeniusPower p 1` into
`rho.symmetricPower p`, for every affine test algebra and test point. The
existing all-test range-stability theorem gives
`isStableSubspace_symmetricFrobeniusSubspace` without passing to rational
points or assuming reducedness.

`exists_equivariantProjection_symmetricFrobeniusSubspace` assumes
semisimplicity of this actual symmetric-power representation in the exact
stable-subspace sense. The existing stable-complement equivalence supplies
a stable complement, and the published equivariant-projection correspondence
constructs a projection onto the Frobenius range intertwining the action on
all affine tests. The theorem assumes the symmetric power's semisimplicity;
it does not yet assert that the task's finite-coordinate definition of
linear reductivity supplies it, or compare the resulting projection with
an alpha_p infinitesimal action.

This is an internal coordinate implementation of the stable Frobenius
subspace and splitting used in the source. It does not assert inheritance
of linear reductivity by arbitrary closed subgroups or prove Nagata's
structural necessity direction.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, proof of Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
