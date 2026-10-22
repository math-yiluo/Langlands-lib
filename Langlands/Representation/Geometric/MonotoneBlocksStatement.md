# Consecutive positive blocks of a monotone finite map

Author: Worker 245. This statement imports the published
`Langlands.Representation.Geometric.WeylDefinitions` pair by Worker 14,
which itself imports the published `Langlands.Group.GL.Blocks` pair by
Worker 6. Both pairs are reused by their current Library module names,
unmodified, with their original authorship. No new data definition is
introduced.

## Statement

`MonotoneBlockShapeTheorem` asserts: for all natural numbers `k` and `l`
and every monotone map `f : Fin k → Fin l`, there is an actual
`S : BlockShape k` such that for all coordinates `a b : Fin k`,

`blockIndex S a ≤ blockIndex S b ↔ f a ≤ f b`.

Here `BlockShape k` is an ordered list of positive block sizes with total
`k`, and `blockIndex S a` is the block containing the coordinate `a`
under the existing standard consecutive numbering `S.indexEquiv` of
`WeylDefinitions` (block `0` first, then block `1`, and so on). No
arbitrary enumeration of coordinates is chosen: the blocks are the actual
consecutive coordinate intervals of `S`.

Because both sides are linear-order comparisons, the equivalence also
gives, by antisymmetry and by negation, for all `a b`:

- `blockIndex S a = blockIndex S b ↔ f a = f b`, so the blocks of `S` are
  exactly the nonempty fibers of `f`;
- `blockIndex S a < blockIndex S b ↔ f a < f b`, so the blocks are ordered
  as the values of `f`.

These two consequences are explanations of the stated equivalence, not
separate Lean clauses. The target `l` is arbitrary. The source `k = 0`
is allowed; there the block shape has no blocks and the comparison
condition is vacuous. The statement asserts existence only; it does not
assert uniqueness of `S` and supplies no chosen construction.

## Provenance and intended use

This is an internal, derived statement of elementary finite order theory,
not a claim taken from a cited source. Its mathematical content is the
standard fact that each nonempty fiber `f⁻¹(v)` of a monotone map on the
linear order `Fin k` is convex, hence a consecutive interval of
coordinates, and that these intervals occur in the order of their values
`v`. Listing the sizes of the nonempty fibers in increasing order of `v`
gives positive sizes with total `k`, which is a `BlockShape k` whose
consecutive blocks are precisely those fibers. This sketch explains why
the proposition is expected to be true; no proof is supplied here.

The statement is a prerequisite for the proof of the published
`Langlands.Geometric.PadicStandardIntersectionsTheorem` in
`Langlands.Representation.Geometric.WeylStatement`, whose pair cites
Bernstein and Zelevinsky 1977, lemma 2.11(b) and section 6.3 (literature
ID `bernstein-zelevinsky-1977-induced-i`). That proof is task
`5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` of Worker 125. It applies this
statement, in each source block `i`, to the monotone map
`a ↦ blockIndex C (w (B.index i a))`, to obtain the refinement of the
block `i` by the target blocks. This finite order fact is internal
infrastructure for that type-A matrix argument and is not cited from the
source.
