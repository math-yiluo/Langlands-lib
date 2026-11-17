# The inverse-transpose twist of an archimedean module

This internal construction pulls a compact action back by `compactIota` and a
Lie action back by `complexifiedMatrixLieIota`, both defined in
`TransposePairing`. The carrier has arbitrary universe `uV`. The complex
case retains the entire scalar extension of the underlying real matrix
Lie algebra.

`transposeTwistRep` is the representation `k ↦ ρ(compactIota k)`.
`transposeTwistLie` is the Lie representation
`X ↦ π(complexifiedMatrixLieIota X)`. Applying either construction twice
recovers the original action. These statements are equalities of the
actual representations and Lie homomorphisms.

The module proves that twisting preserves `IsRealGKModule` and
`IsComplexGKModule`, and, for either field, `IsIrreducibleGKModule` and
`IsAdmissibleGKModule`. The corresponding equivalences follow by twisting
twice. No irreducibility or admissibility is needed to preserve the module
conditions themselves.

The proof of compact finiteness identifies the two orbit spans: inverse
transpose permutes the compact group. Matrix coefficients remain
continuous because on a unitary matrix inverse transpose is entrywise
conjugation. For differentiation, differentiating `γ(t)* γ(t) = 1` at the
identity proves `star(X j i) = -X i j` for a tangent matrix `X`.
Consequently entrywise conjugation of the curve has derivative `-Xᵀ`,
which is the actual differential required by the twisted Lie action.
Negative transpose carries compact adjoint conjugation to conjugation by
the twisted compact matrix; this gives the covariance condition.

Irreducibility follows because stable subspaces are unchanged after
pullback by the two involutions. For admissibility the module identifies
the intertwiner space from a continuous finite dimensional compact
representation `τ` into the twisted representation with the intertwiner
space from `τ ∘ compactIota` into the original representation. The latter
has finite dimension by the given admissibility hypothesis.

The provenance is internal: these elementary constructions and
transport proofs use the existing matrix involutions and the exact
Library module predicates. They do not establish existence of a
transpose invariant pairing, globalization, or contragredient
identification.
