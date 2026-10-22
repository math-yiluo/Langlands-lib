# The actual single-block Levi and its refinements

Author: Worker 163.

This pair constructs the geometry needed by the published
`Langlands.CuspidalSupport.SingleBlockCuspidalityClause`. It imports
`Langlands.Representation.Geometric.WeylDefinitions` and thereby the existing
actual block matrices from `Langlands.Group.GL.Blocks`. Those Library pairs
are unchanged. All declarations below are in
`Langlands.GeneralLinear.BlockShape`.

For every rank `n`, every `B : BlockShape n` with `hB : B.length = 1`, and
every commutative ring `R`, the pair constructs an equivalence from
`B.Levi R` to the actual `Langlands.GeneralLinear n R`. In particular it
applies to every field. There is no extra positive-rank premise: the
positivity already required of every block rules out a one-block shape
of rank zero. No representation hypotheses enter these constructions.

## The embedding and its continuous inverse

`singleBlockIndex B hB` is the index with value zero.
`eq_singleBlockIndex` proves that every block index equals it.
`singleBlock_size` uses the shape's sum equation to prove that the sole
block has size `n`. `singleBlock_index_val` uses Mathlib's
`finSigmaFinEquiv_one` to show that the actual consecutive-block numbering
preserves coordinate values in this block.

`singleBlock_parabolic_eq_top` proves `B.parabolic R = ⊤`: the strictly
lower block conditions have no index pairs on which to impose a zero.
`singleBlock_leviEmbedding_projection` then proves that embedding the
existing Levi projection recovers every parabolic matrix. Its proof
writes both matrix coordinates using `B.indexEquiv`, identifies their
block indices, and uses the existing diagonal-entry formula for
`leviEmbedding`.

`B.singleBlockLeviEquiv hB R` has forward map exactly
`B.leviEmbedding R`. Its inverse includes an arbitrary matrix in the
now-proved full parabolic and applies `B.leviProjection R`. The left
inverse law is the published projection-section law, and the right
inverse law is the matrix-entry calculation above. The lemma
`singleBlockLeviEquiv_toMonoidHom` identifies the homomorphism by
reflexivity. `singleBlock_leviEmbedding_surjective` exposes surjectivity
of the actual embedding.

With `[TopologicalSpace R] [IsTopologicalRing R]`,
`B.singleBlockLeviEquivContinuous hB R` equips this same equivalence with
both continuity proofs. The forward direction uses the published
continuous embedding. The inverse is the continuous inclusion into the
full parabolic followed by its published continuous Levi projection.
`singleBlockLeviEquivContinuous_toMonoidHom` again identifies the actual
homomorphism by reflexivity. No Hausdorff or local compactness assumption
is needed.

## Refinement correspondence and subgroup laws

`rankCast C h` changes only the asserted total rank of a shape along an
equality `h`; its ordered sizes remain the same. The equivalence

```lean
B.singleBlockRefinementEquiv hB :
  Langlands.Geometric.BlockRefinement B ≃ BlockShape n
```

takes a refinement to its sole component, transported along
`singleBlock_size`. Its inverse transports any `C : BlockShape n` to
the rank of each block of `B`. The inverse laws follow by equality of
all block indices and the unchanged ordered sizes. Thus every ambient
shape occurs, with an explicit inverse construction.

For `C = B.singleBlockRefinementEquiv hB S`,
`singleBlockRefinement_index` proves that `C.index j a` is exactly
`B.index (B.singleBlockIndex hB) ((S (B.singleBlockIndex hB)).index j a)`.
This uses preservation of coordinate values and the definition of rank
transport. It is an equality of the actual standard coordinates.

`singleBlock_mem_refinedParabolic_iff` identifies membership of `m` in
`Geometric.refinedParabolic R B S` with membership of
`B.leviEmbedding R m` in `C.parabolic R`. The proof expands the product
subgroup membership, applies the coordinate identity, and uses the
published zero-entry characterization of parabolics.
`singleBlock_mem_refinedUnipotent_iff` proves the analogous equivalence
for `refinedUnipotent` and `C.unipotentSubgroup R`, combining that
parabolic calculation with the published identity-diagonal-block
characterization of the ambient unipotent subgroup.

Surjectivity of the actual embedding turns these membership equivalences
into both requested image equalities, with the same shape `C`:

```lean
(Geometric.refinedParabolic R B S).map (B.leviEmbedding R) = C.parabolic R
(Geometric.refinedUnipotent R B S).map (B.leviEmbedding R) = C.unipotentSubgroup R
```

Their names are `singleBlock_refinedParabolic_map` and
`singleBlock_refinedUnipotent_map`. The lemma
`singleBlock_refinedParabolic_ne_top_iff` proves
`Geometric.refinedParabolic R B S ≠ ⊤ ↔ C.parabolic R ≠ ⊤`.
One direction uses the image of the top subgroup under a surjection;
the other uses the membership equivalence. For an arbitrary ambient
shape `C`, use `S = (B.singleBlockRefinementEquiv hB).symm C` and the
equivalence's `apply_symm_apply` law in all three results.

## Provenance and scope

The source convention is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), sections 2.1–2.2,
printed page 446 (PDF page 7). Section 2.1 fixes the standard parabolic
triple in a standard Levi, and section 2.2 identifies GL standard Levis
with ordered partitions and their standard subgroups with refinements.
The retained original page was read, including sections 2.3–2.4, which
explain the surrounding Jacquet and cuspidality application.

Registered source: `bernstein-zelevinsky-1977-induced-i`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The one-block identifications are derived constructions, not a separately
numbered theorem quoted from BZ77. The extension from local fields to
commutative rings, dependent rank transport, entrywise proofs, and
continuity certificates are internal derivations from the imported
Library definitions and Mathlib. This pair proves their intrinsic laws.
It does not prove the representation, admissibility, coinvariant, or
cuspidality comparisons; those use this geometry in the parent task.
