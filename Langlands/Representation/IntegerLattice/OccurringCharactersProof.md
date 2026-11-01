# Full-lattice eigencharacters and their finite complete enumeration

Worker 1214 proves the exact published proposition
`Langlands.RenardCIIIOccurringCharactersStatement.{u}` with the closing theorem
`Langlands.renardCIIIOccurringCharacters.{u}`. The statement and its imports are
unchanged. The three component theorems establish reconstruction and
injectivity, the arbitrary-dimensional same-vector comparison, and the single
finite enumeration of both actual nonzero blocks and occurring characters.

## Implemented proof

`lattice_eq_prod_generators` writes each point of the actual lattice
`Multiplicative (Fin d → ℤ)` as the product of its standard generators raised
to its integer coordinates. Passing to additive coordinates reduces this
identity to the coordinatewise sum of the corresponding single-coordinate
vectors. This is the elementary lattice identity also used in the published
global block-basis proof; no block basis is needed here.

`coordinateCharacter_reconstruction` applies an arbitrary character to that
product. Preservation of products and integer powers gives exactly the
published coordinate-character formula. `coordinateCharacter_injective`
evaluates equality of two coordinate characters on each standard generator.
These arguments require no occurrence or finite-dimensional assumption.

`commonEigenvector_iff_coordinateCharacter` fixes the vector and forms the
subgroup of lattice points at which the action agrees with its coordinate
character on that same vector. The identity belongs to it. Linearity and the
representation and character multiplication laws close it under products.
For inverses, applying the invertible representation operator reduces the
claim to cancellation of a nonzero complex unit and its inverse. The generator
eigenvector equations put all standard generators in this subgroup. Its
closure under integer powers and products, together with the lattice product
identity, covers every lattice point. Conversely, evaluating at generators
recovers the original eigenvector equations. This argument includes the zero
vector, negative coordinates and mixed-sign coordinates, and assumes no finite
dimension.

`commutingTupleOccurringCharacterEnumeration` takes the finite support from
`Langlands.commutingTupleGeneralizedWeightDecomposition` and reindexes its
subtype by `Fin (Fintype.card S)`. This chooses one list `c` of exactly all
labels of actual nonzero `generalizedWeightBlock A b`. The subtype inclusion
and the reindexing are injective; coordinate-character injectivity therefore
makes the indexed characters distinct.

For an arbitrary full-lattice character realized on a nonzero vector, evaluate
its action at generators and let `b` be these generator values.
`Langlands.commutingTupleGeneralizedWeightSupport` places `b` in the actual
nonzero block support. The same finite list contains `b`, and reconstruction
identifies its coordinate character with the original character. Conversely,
each label on that list has a nonzero common generator eigenvector by the
same support theorem. The same-vector comparison extends its action to the
whole lattice. Thus both directions of the block and occurring-character
comparisons use this one list.

## Scope and provenance

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix C.III, printed pp.279–280 / one-based
PDF285–286. The proof paragraph on p.279 passes from common eigenspaces to
their full-lattice scalar characters and lists all the distinct characters;
p.280 uses those characters to label simultaneous triangular blocks. Both
pages were read directly for this proof. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

Character reconstruction is an elementary derived coordinate formulation.
The identification with actual generalized-weight support is a derived
basis-free formulation, using the independently published support and
decomposition proofs. The same-vector comparison in arbitrary dimension is
an explicit internal generalization of the source's finite-dimensional
setting. This proof does not add finite dimension or nonzero-vector
hypotheses to that comparison. The enumeration alone assumes finite dimension.

Every natural rank and arbitrary carrier universe `u` are retained. The
support subtype is empty in the zero space, so the chosen list is empty.
At rank zero there is one possible label, its actual block is the whole
space, and the chosen list therefore has one entry precisely when the space
is nonzero. Zero blocks never enter the support subtype. No positivity,
nontriviality, supplied support list, common eigenvector, basis, decomposition,
nilpotence or desired conclusion is required from the caller.

The proof uses the actual tuple action, generators, unit-valued coordinate
characters and generalized-weight blocks imported by Lean name. The final
aggregate is the unchanged plain conjunction of its three published
components. The source-style block-matrix polynomial assembly and the other
Appendix C.III and whole-book obligations remain separate.
