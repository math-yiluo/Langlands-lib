# Matrix containments for consecutive block coarsenings

Author: Worker 534.

The theorem `Langlands.glBlockCoarseningSubgroups` proves exactly
`Langlands.GLBlockCoarseningSubgroupStatement`, with arbitrary ring universe
`uR`. For every rank, two actual block shapes, and a monotone surjection whose
fibers have the prescribed coarse sizes, the fine parabolic and fine Levi
subgroup are contained in the coarse ones over every commutative ring.
There is no positivity assumption on the total rank, no nontriviality assumption
on the ring, and no hypothesis about a real exponent vector.

The proof is internal elementary matrix and finite-order reasoning. It uses
the published block matrix definitions and coordinate lemmas, and does not
assume any root/weight cone existence or uniqueness theorem.

The first private helper says that monotone functions from `Fin m` to a
finite linear order with the same fiber cardinalities coincide. Choose
equivalences between corresponding fibers. Their union is a permutation of
`Fin m` that carries one function to the other. Mathlib's
`Tuple.unique_monotone` identifies the resulting sorted tuples.

The second private helper counts the standard coordinates whose fine block
labels map to a given coarse label. Reindexing through the actual block
coordinate equivalence gives exactly the sum of the fine block sizes over that
fiber. The public theorem `blockIndex_coarsening` compares these counts with the
coarse coordinate counts and applies the first helper. It proves that each
standard coordinate has coarse label equal to the image of its fine label.
This coordinate identity uses monotonicity and the size equations;
surjectivity is unnecessary for this intermediate result.

The proof reuses the published theorem
`Langlands.Geometric.mem_parabolic_iff_blockIndex` from
`Langlands.Representation.Geometric.StandardIntersectionsProof`. It translates
the block-coordinate criterion to standard matrix entries: an entry vanishes
whenever its column block precedes its row block.
The public theorem `mem_leviSubgroup_iff_blockIndex` characterizes the actual
embedded Levi by vanishing between distinct block labels. In the forward
direction this follows from the Levi embedding's entry formulas. For the
converse the zero entries first give parabolic membership. Its Levi projection
extracts the invertible diagonal blocks, and reembedding that projection
recovers the whole matrix by entrywise equality.

Finally, if a coarse column label precedes a coarse row label, monotonicity
forces the corresponding strict order between their fine labels, so the fine
parabolic entry criterion supplies the required zero. Distinct coarse labels
also force distinct fine labels, so the Levi entry criterion transfers in the
same way. These two implications prove the stated subgroup containments.
