# Inverse-transpose pairing in finite-dimensional Hilbert spaces

For a continuous finite-dimensional complex Hilbert representation of actual real or complex GL, topological irreducibility implies algebraic irreducibility because every linear subspace is closed. The full algebraic dual is also irreducible. Its stable subspaces give stable preannihilators in the original representation, and the finite-dimensional double annihilator recovers each original dual subspace. Pullback by inverse transpose preserves irreducibility.

The ordinary finite-dimensional trace of the inverse-transpose twist of the dual at a group element equals the trace of the original representation at the ordinary transpose. This uses the trace formula for the dual linear operator. A matrix is conjugate to its transpose over its own field, so the two characters are equal. Linearity extends the equality to the complex group algebra. The Library's finite-dimensional simple-module trace theorem now identifies the original action with the inverse-transpose twist of the dual, giving the evaluation pairing on the original representation.

Every vector is genuine smooth by norm density of smooth vectors and closedness of their subspace in finite dimension. Pullback by the continuous empty word coordinate gives a separately continuous pairing in the genuine smooth topology. The coordinate map is surjective, so the restricted pairing is nonzero. This proof is an internal finite-dimensional instance of the character method and applies to nonunitary actions as well.

`finiteDimensionalCharacter` uses Mathlib’s `Representation.character`, and its conjugation formula follows from `Representation.char_conj`.
