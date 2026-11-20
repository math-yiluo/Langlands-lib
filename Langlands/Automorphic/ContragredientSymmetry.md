# Symmetry of the contragredient relation for cuspidal realizations

Worker 814, Task 5978.

`Langlands.Automorphic.CuspidalContragredientSymmetryStatement` says that if
`T` realizes the contragredient of `S`, then `S` realizes the contragredient
of `T`. It applies to actual cuspidal realizations of the same rank over any
number field with compact adele quotient. The proof
`cuspidalContragredientSymmetry` applies
`CuspidalOperatorRealization.isContragredientOf_symm` to the given
realizations. Swapping `S` and `T` supplies the reverse implication.

If `T` realizes the contragredient of `S`, take the pairing `B` from the
definition. Exchanging the arguments preserves invariance for the finite
adelic group and the archimedean compact subgroup. It exchanges the two
summands of the real Lie invariance identity. The transposed pairing is
nonzero because the partial map `B.flip` is injective and the space of `T`
is nontrivial by irreducibility. The published
`isContragredientOf_of_nonzero_invariant` criterion for actual cuspidal
realizations now makes `S` a contragredient of `T`. That criterion uses
existence of actual cuspidal contragredients and Schur's lemma.

This is a derived lemma for the passage from Getz and Hahn (2024), Theorem
11.7.1 (printed p. 309, registered PDF p. 320), to Lemma 11.8.1 (printed
p. 312, PDF p. 323), source `getz-hahn-2024-automorphic-representations`.
The pole profile takes the first realization to be the contragredient of
the second. The multiplicity counts indices for which the second is the
contragredient of the first. Worker 3657's Task 5978 draft identified the
needed reversal. Worker 770 independently suggested applying the published
invariant-pairing criterion to the transposed pairing.
