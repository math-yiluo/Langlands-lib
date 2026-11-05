# Coordinate height of actual uniformizer charts

`Langlands.Plancherel.RationalUniformizerCoordinateHeightStatement.{u,uI}`
is an internal geometric estimate for the coefficientwise moderate-growth
proof. The field and finite coordinate type have independent universes.

Let `i : S → G` be a closed inclusion of an actual commutative group scheme
over a nonarchimedean local field `F`, and let `ρ : G → GL(n)` be any supplied
closed embedding, with finite nonempty matrix index. Choose finitely many
actual cocharacters `x_j` of `S` and an actual character `α` of `S` such that
`⟨α,x_j⟩ > 0` for every `j`. Write `q` for the residue cardinality and evaluate
all cocharacters at the same chosen uniformizer. There are a natural exponent
`d` and a positive real constant `c`, independent of the natural tuple `m`,
such that

`q^(sum_j m_j) ≤ c * rationalMatrixNorm F ρ (i((sum_j m_j x_j)(π)))^d`.

The norm uses the actual rational-point matrix and its inverse with the
residue-normalized absolute value. No representation, admissibility,
finite-length, splitness, reductivity or characteristic restriction is imposed.
The index type may be empty; then the left side is one and the uniformizer
point is the identity. The character and cocharacters are supplied rather than
asserted to exist.

The internal derivation uses the regular function given by the inverse of `α`
on `S`. Its uniformizer magnitude is `q^(sum_j m_j ⟨α,x_j⟩)`. Each positive
integer pairing is at least one. The regular-function polynomial estimate for
the closed embedding `ρ` restricted to `S` therefore gives the claimed bound.
This is a derived prerequisite, not an independently attributed literature
statement. It supplies the coordinate-to-matrix-norm estimate for any such
chart, while leaving chart existence, central-direction charts, the global
Cartan cover and all coefficient estimates as separate obligations.
