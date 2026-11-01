# Uniform local repeated-factor triple transfer

This internal interface isolates the local representation-theoretic input for
`Classification.RepeatedCuspidalTripleJacquetTransfer`. It is a proposition
definition, without a proof of either local move.

For every positive rank `d`, the proposition considers an actual irreducible,
admissible, finite-length smooth representation `E` of `GL_(d + (d + d))`,
and three supplied rank-`d` supercuspidal representations `A`, `B`, and `C`.
The initial hypothesis is an actual subquotient occurrence of the tensor
`A ⊗ B ⊗ C` in the normalized upper Jacquet module of `E` for the standard
shape `threeBlocks d d d`. The relation `[A] = ν[B]` uses the determinant
real-power twist attached to the supplied topological data.

The first clause assumes `[C] = [B]` and asks for the actual tensor
`B ⊗ A ⊗ C` in the same Jacquet module. The second assumes `[C] = [A]` and
asks for `A ⊗ C ⊗ B` or `B ⊗ A ⊗ C`. Each occurrence retains the supplied
representative `C`; class equality does not replace its carrier or action.
`uniformTripleTensor` is the existing external smooth tensor applied to
`Parabolic.threeBlockSmoothFamily`.

The provenance is internal: this is the uniform three-block specialization
needed after actual coarse constituent extraction in the ambient task. Its
two clauses match the local order changes named by the published ambient
statement. No claim is made here that a printed source proves this interface,
that the local input has been established, or that the ambient task is complete.
The field and representation universes are independent; the ambient theorem
will specialize the latter to `max uF uV`.
