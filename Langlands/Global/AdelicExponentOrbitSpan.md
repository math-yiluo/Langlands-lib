# Split-component translates of weak constant terms

`AdelicExponentOrbitSpanStatement` says that each component of a finite sum with distinct
normalized generalized exponents belongs to the complex span of the left positive
split-component translates of the sum. The polynomial orbit condition of Delorme's
equation (3.2) places the components in joint generalized eigenspaces, with the half modulus
added to the exponents for the unnormalized action.

`adelicExponentOrbitSpan` uses the quotient representation by the invariant orbit span. The
sum maps to zero there, and distinct parameters give distinct eigenvalue functions on the
positive split component. Directness of the joint generalized eigenspaces forces every
component to map to zero. The same argument puts the sum of the components with unitary
exponents, defined by Delorme's Definition 3.7, in the orbit span of the ordinary constant term.

The span is the range of evaluation at the generating function of the complex group-algebra
action. When the generating function is automorphic on a parabolic quotient, this action
preserves automorphy. For nested parabolics the split component of the larger parabolic maps
into that of the smaller one, and its action commutes with the smaller ordinary constant
term on the parabolic quotient. The shift preserves every normalized exponent of the smaller
constant-term decomposition. Consequently taking the sum over unitary labels commutes with
the shift as well.

The source is P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426
(2023), 109107, equation (3.2), PDF p. 10, and Definition 3.7, PDF p. 13.
The registered PDF is `Delorme--On the spectral theorem of Langlands--2023.pdf`,
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`,
under `delorme-2023-spectral-theorem-langlands`.
