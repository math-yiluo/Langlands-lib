# Elementary fixed-vector reductions for Howe's implication

Worker 1210, in coordination with Worker 189.

This internal statement unit isolates two elementary steps used in the forward
implication of Renard VI.6.3. Its declarations are proposition definitions;
the unit does not prove them or assert the reductive-group detection input.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The theorem and preceding assertions are on printed pages 178–179,
PDF pages 184–185. The finite-generator choice and fixed-vector chain argument
are in the forward proof on printed page 179 / PDF185. That passage was read
in full. The formulations here are derived internal algebraic reductions of
those two steps, using the Library's actual group-algebra and composition-series
conventions. They are not new assertions attributed verbatim to the source.

`CommonFixedGeneratorsStatement` quantifies independently over a commutative
coefficient ring `R`, a group `G` with a topology, a module carrier `V`, and an
actual representation `ρ`. Its premises are smoothness and finite generation
of `ρ.asModule` over `MonoidAlgebra R G`. It asserts a finite family of vectors
whose actual group-algebra span is the whole module, and an open subgroup fixing
all those vectors. For every subgroup contained in that open subgroup, its fixed
vectors generate the representation: any invariant subspace containing them
equals the whole representation. This assertion requires no compatibility
between the topology and the group operations.

`FixedVectorsStrictInclusionLengthStatement` quantifies independently over a
field `R`, a group `G`, a module carrier `V`, an actual representation `ρ`, and a
subgroup `K`. Its premises are finite dimension of `fixedVectors ρ K` and the
explicit detection condition that every strict inclusion `S < T` of actual
subrepresentations has a vector in `T` fixed by `K` that does not lie in `S`.
It concludes both an actual composition series with length at most
`Module.finrank R (fixedVectors ρ K)` and finite length of the actual
`MonoidAlgebra R G` module. There is no topology or smoothness premise in this
algebraic statement. The zero representation and the zero-dimensional
fixed-vector space are included.

`FixedVectorLengthReductionStatement` is their conjunction with the same three
independent universe parameters. The unrestricted rational-point Howe target,
its topology and its imported files are unchanged. The reductive-group step
producing detection from finite generation and admissibility, the VI.6.3
intermediate assertions, and the source's stronger bound for its specially
chosen compact open subgroup remain separate proof obligations. In particular,
the first statement only constructs an open subgroup; it does not construct the
normal compact subgroup with simultaneous Iwahori decompositions.
