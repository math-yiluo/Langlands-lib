# Compact-open finite containment in block unipotent radicals

Worker 201 proves `Langlands.Parabolic.unipotentFiniteContainment`, whose type
is exactly the published `Langlands.Parabolic.UnipotentFiniteContainmentClause
F T B`. The parameters are every prime `p`, every `F : PadicField.{uF} p`,
every compatible `T : F.TopologicalData`, every natural rank `n`, and every
`B : GeneralLinear.BlockShape n`. The field universe is unrestricted. All
topologies in the conclusions are induced by precisely `T.topology`.

For every finite subset of `B.unipotentRadical F.Carrier`, the theorem produces
an open subgroup containing that subset and proves its underlying set compact.
The intrinsic radical remains the published kernel subgroup of the actual
parabolic. The statement pair and its import closure are unchanged. No
exhaustion, contraction, finite-containment, or other geometric conclusion is
assumed. This module does not prove a nested exhaustion or quotient compactness.

The same unit proves the required finite-product consequence
`Langlands.PadicField.TopologicalData.refinedUnipotent_finite_containment T B S`
for every `S : Langlands.Geometric.BlockRefinement B`. Its finite subsets and
compact open subgroups belong to the actual
`Langlands.Geometric.refinedUnipotent F.Carrier B S`, with its product-Levi
subgroup topology. There is no properness assumption on `S`, and no positive
rank assumption.

## Implemented proof

1. The existing `Langlands.RankinSelberg.common_integer_denominator` finds a
   nonzero integral scalar `d` clearing
   any finite set of field elements. For one element `x`, use `1` when `x` is
   integral, and `x⁻¹` otherwise. The valuation-ring dichotomy makes the second
   choice integral. Multiplying denominators handles a finite union.
2. For a finite subset of the radical, gather all entries of every matrix
   and its inverse, and clear their denominators simultaneously. Set the
   scalar on block `i` to `d^(-i)`, as a unit with integer exponent, and let
   `D` be the existing `B.blockScalar` matrix. The published
   `blockScalar_conj_apply` computes the `(i,j)` block of `D g D⁻¹` as
   `d^(-i) d^j g_ij`. If `i < j`, this is
   `d^(j-i-1) (d g_ij)`, hence integral. On a diagonal block the entries are
   those of the identity; below the diagonal they vanish. These claims use
   the actual radical and parabolic membership characterizations and do not
   assume that the block index equivalence preserves an order.
3. Pull the compact open integral subgroup of the ambient general linear
   group back along the homomorphism `g ↦ D g D⁻¹`, restricted to the radical.
   This map is continuous and a closed embedding: the radical is closed in
   the parabolic, the parabolic is closed in the general linear group, and
   conjugation is a homeomorphism. The pullback is therefore compact and open.
   The integral subgroup criterion checks both a matrix and its inverse;
   step 2 applies to both using the same scalar `d`.
4. The ambient integral subgroup API uses ranks `n+1`. Rank zero is handled
   directly: its radical is finite (indeed a singleton), so the whole group
   is compact and open. Empty finite subsets at every rank are included.
5. `GeneralLinear.BlockShape.unipotentRadicalAmbientEquiv` constructs the
   continuous multiplicative equivalence between an intrinsic radical and
   its actual ambient image `unipotentSubgroup`. Its forward map forgets the
   intermediate parabolic membership, and its inverse reconstructs that
   membership and the kernel condition from the existing matrix criteria.
   Both continuity proofs use the actual nested subtype topologies.
6. `Geometric.refinedUnipotentRadicalEquiv` applies that equivalence in each
   factor, identifying the actual refined subgroup with the dependent finite
   product `∀ i, (S i).unipotentRadical F.Carrier`. Its maps and continuity
   proofs are constructed explicitly. Apply the main theorem to the finite
   image in each factor, form the product of the resulting compact open
   subgroups, and pull it back through this equivalence. Compactness follows
   from product compactness and the homeomorphism; openness follows from the
   finiteness of the block index set. The construction works for the empty
   product as well.

The auxiliary equivalences and finite-product consequence are internal derived
constructions supporting this proof unit. They are not assumptions on the
field, topology, block shape, or refinement.

## Provenance and sources

The denominator lemma is reused directly from the published work of Worker 117
in
`Langlands.Representation.RankinSelberg.UnipotentUnimodularity`, especially
`common_integer_denominator`, `scalingDiagonal_conj_integral`, and
`unipotent_exists_compact_open`; the latter two supply the diagonal-conjugation
proof organization adapted here. Worker 117 is credited as a coauthor for this
reused proof text. That earlier module credits Worker 103 for suggesting the
compact-open-subgroup route. The present generalization clears a finite set
at once, scales by block index, handles rank zero separately, and constructs
the refinement transports. It imports no unpublished proof or draft.

The original geometric source is Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
Lemma III.3.1 and its proof, printed/PDF page 3. Source ID:
`casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original proof expands compact open subgroups of upper unitriangular
matrices using uniformizer diagonal conjugation, then takes closed subgroups.
The implemented proof uses finite denominator clearing instead of constructing
a uniformizer-indexed sequence; it proves the specified finite-containment
consequence directly.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Proposition 2.3(a), printed page 446/PDF page 7, uses the compact
exhaustion of the radical in the proof of Jacquet exactness. Source ID:
`bernstein-zelevinsky-1977-induced-i`; SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
This explains the intended downstream use; the module does not prove that
exactness theorem. Both original pages were read. No errata files for either
source were present in the current Library.
