# Matrix proof of standard intersections

Authors: Worker 125 and Worker 165. Worker 125 implemented the coordinate,
conjugation, and refinement assembly arguments. The Levi membership argument
uses Worker 165's published `Langlands.CuspidalSupport.levi_mem_iff` directly.

`Langlands.Geometric.padicStandardIntersectionsTheorem` proves the exact
published proposition `Langlands.Geometric.PadicStandardIntersectionsTheorem`
from `WeylStatement`. For every prime, actual p-adic field, positive rank,
pair of positive ordered block shapes, and actual minimal permutation, it
constructs positive block refinements on both sides and proves all six
parabolic, Levi, and unipotent subgroup equalities.

The proof imports `Langlands.Geometric.monotoneBlockShape` from Worker 175's
`MonotoneBlocksProof`. This supplies the finite-order existence theorem;
no theorem-truth hypothesis remains in the final theorem or in
`exists_standardIntersections`. All published source pairs are unchanged.

## Implemented argument

The coordinate identity `blockIndex_index` comes from `WeylDefinitions`.
`index_blockIndex` follows from the inverse law of the coordinate equivalence;
`index_ne_of_block_ne` follows by applying `blockIndex` to a hypothetical
equality. The published `blockIndex_monotone` from `WeylUniquenessProof`
expresses the order of the standard consecutive blocks.

The parabolic criterion `mem_parabolic_iff_blockIndex` records zero entries
below the diagonal block order. The Levi criterion `CuspidalSupport.levi_mem_iff`
records zeros between distinct blocks. Its imported proof recovers a matrix
with this zero pattern by embedding its parabolic Levi projection. The
unipotent criterion `mem_unipotent_iff_blockIndex` combines parabolic
membership with identity entries within each block. These criteria hold over
every commutative ring, including the trivial ring.

Permutation conjugation permutes row and column indices. An embedded product
Levi has zero entries between distinct outer blocks, so zero and identity
conditions on its conjugate reduce to conditions on each individual outer
block. For the identity condition, coordinates in distinct outer blocks are
distinct, so the corresponding entry of the identity matrix is also zero.
These reductions yield the three `mem_source..._iff` lemmas for the actual
subgroup preimages under `conjugatedLeviMap`.

`standardIntersections_of_comparisons` takes an actual refinement `S` whose
block-index comparisons agree with those of `blockIndex C ∘ w ∘ B.index i`
inside every outer block. Agreement of weak order also gives agreement of
strict order and equality. Applying the three coordinate criteria and
subgroup extensionality proves the actual parabolic, Levi, and unipotent
subgroup equalities. No subgroup equality is an input to this transfer.

`exists_standardIntersections` assumes the permutation is strictly increasing
within each source block. Composing this property with monotonicity of the
target block-index map gives a monotone finite label map on each source block.
The imported `monotoneBlockShape` supplies an actual positive consecutive
block shape with exactly the same order comparisons. Choosing one such shape
for each source block gives `S : BlockRefinement B`, and the comparison-transfer
lemma proves all three equalities for that same refinement.

The closed theorem `padicStandardIntersectionsTheorem` applies this construction
to `B, C, w` using the first minimality condition, and to `C, B, w⁻¹` using the
second. Specializing the ring to each actual p-adic field's carrier gives the
six equalities in the published statement. The reusable one-sided theorem
works over every commutative ring and every natural rank; the closed theorem
retains the exact p-adic, positive-rank quantifiers of the target. It neither
assumes subgroup identifications nor substitutes abstract isomorphic groups
for the actual refinements.

## Provenance

This is an internal matrix implementation of the GL specialization of
Bernstein–Zelevinsky (1977), Lemma 2.11(b), printed page 448 (PDF page 9), and
sections 6.1–6.3, printed pages 467–468 (PDF pages 28–29). The original passages
were read. Source ID: `bernstein-zelevinsky-1977-induced-i`; SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The proof uses the existing concrete block and permutation definitions.
Its matrix and finite-order arguments implement the standard-intersection
assertion without using the general root-system proof in the source.
No irreducibility or representation-theoretic corollary is asserted.
