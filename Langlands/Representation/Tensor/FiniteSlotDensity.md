# Irreducibility from dense operator algebras in the tensor factors

`slotAlgebraHom` applies an endomorphism in one factor of an indexed
tensor and identity maps in every other factor. Invariance of a subspace
under the indicated generators in a slot extends to the generated
algebra because the slot map respects linear combinations and composition.

For a finite index type, `eq_top_of_slot_density` uses density on each
finite set of vectors in a tensor basis expansion. Take a nonzero
coefficient in the expansion of a vector in the invariant subspace.
To produce a given pure tensor, use a rank-one coordinate map in each
factor. The tensor of these maps selects the chosen coefficient and
sends the selected basis tensor to the prescribed pure tensor. Replace
each coordinate map by a generated operator that agrees on the finite
support of the expansion. The resulting tensor map preserves the
subspace and has the same value on the given vector. Dividing by the
nonzero coefficient puts the pure tensor in the subspace. Pure tensors
span, so the subspace is the whole tensor.

This is the finite tensor argument in the Library's
`FiniteTensor.isIrreducible_external` applied to given operator generators.
It accommodates both group operators and complexified Lie operators.
The tensor-product application is motivated by the constituent
construction of Langlands (1979), Lemma 1, printed p. 203 (PDF p. 198).
