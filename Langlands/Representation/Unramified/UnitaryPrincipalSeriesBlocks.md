# Unitary unramified principal series as tempered blocks

Module `Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks`.
This helper module proves that a normalized principal series of `GL_m(F)`
induced from unramified characters whose uniformizer values have norm one is
irreducible and analytically tempered. These are the two facts a tempered
Langlands block must satisfy. Here `F` is an arbitrary p-adic field with its
canonical topological realization. The proof of
`Langlands.Correspondence.orderedUnramifiedTemperedRealization` uses these
blocks.

Everything below is derived internally from published Library results; no
outside theorem is assumed. The principal series and the lemmas are auxiliary
constructions, not quotations of a source statement.

## Combinatorics and the group `GL_1`

- The existing `BlockShape.singletons m` from `Group.GL.SingletonBlocks` is the block shape `(1, …, 1)` of `GL_m`: it has length `m` and
  every block has size `1`. It is definitionally the shape
  `Correspondence.borelShape r` when `m = r + 1`. The lemma `BlockShape.singletons_index`
  says that the standard coordinate of block `k` is `k`. It is reused from that module.
- `generalLinear_one_mul_comm`: `GL_1(R)` is commutative over any commutative
  ring. Its matrices are `1 × 1`.
- `subsingleton_centralQuotient_one`: hence `GL_1(R) / Z(GL_1(R))` has a single
  point. Every element of `GL_1` is central, so `QuotientGroup.eq` identifies
  any two classes.

## Analytic facts

- `isSquareIntegrable_of_unitaryScalar`: take an admissible representation of
  `GL_1(F)` on which every `g` acts by the scalar `χ(g)`, where `χ` has open
  kernel and `‖χ(g)‖ = 1`. Then it is square-integrable modulo the center for
  every Borel Haar measure on the central quotient (`T.IsSquareIntegrable`).
  The unitary central character is `χ` restricted to the center. The central
  quotient is a point, so it is compact and every Haar measure on it is finite.
  The descended coefficient norm `c.coefficientNorm ℓ v` is therefore a
  constant function, and constants lie in `L²` of a finite measure
  (`MeasureTheory.memLp_const`).
- `isTempered_of_isSquareIntegrable`: square-integrability implies
  temperedness, one Haar measure at a time, by the published
  `isTemperedModCenter_of_squareIntegrable`.
- `isSquareIntegrable_castRank`: transport along an exact rank equality
  `T.castRank h` preserves square-integrability (by `subst`).
- `rankOneUnitary_isSquareIntegrable`: the published rank-one supercuspidal
  object `Correspondence.rankOneSupercuspidalObject F (character F w)` is
  square-integrable when `‖w‖ = 1`. Its action is the scalar
  `T.determinantUnramifiedCharacter 1 w`, which has open kernel
  (`isOpen_ker_determinantUnramifiedCharacter`) and norm one
  (`norm_unramifiedCharacter`). Admissibility comes from the object's
  supercuspidality.

## Segment facts

- `singletonSegment_isSegmentHead`: a supercuspidal representative `A` of a
  cuspidal datum `ρ` is the strong head of the induction of its one-term
  segment. The published `singletonSegmentInducedEquiv` identifies that
  induction with `A` itself, cast along the rank equality. An irreducible
  representation is its own strong head (`Classification.isIrreducibleHead_self`),
  and heads transport along equivalences of the source
  (`IsIrreducibleHead.of_equiv`). This is the head analogue of the published
  `singletonSegment_isSegmentSocle`.
- `unramifiedCuspidalDatum F w` is the rank-one cuspidal datum whose class is
  the isomorphism class of `rankOneSupercuspidalObject F (character F w)`.

## The block and its properties

`unitaryBlock F w`, for `w : Fin m → ℂˣ`, is the actual normalized product
induction `(normalizedProductInductionFunctor (BlockShape.singletons m)).obj` of the
rank-one objects `rankOneSupercuspidalObject F (character F (w k))`. Its
carrier lies in the field universe `uF`.

`unitaryBlock_isIrreducible` (for `0 < m` and `‖w k‖ = 1` for all `k`):

1. Write `m = n + 1` and form the published segment-product datum
   `SegmentProductDatum.ofCuspidals` of the singleton segments of the
   `unramifiedCuspidalDatum F (w k)`. Its blocks are segment socles by
   `ofCuspidals_hasSegmentSocles`.
2. The multisegment is unlinked. Every block is a segment head (previous
   lemma) and is square-integrable (`rankOneUnitary_isSquareIntegrable`, cast
   along the rank equality). The published `squareIntegrableSegmentNonlinkage`
   says that segments whose heads are square-integrable are never linked.
3. The published `segmentSocleProductIrreducibility` is the Library's
   formalization of Zelevinsky 1980, Theorem 4.2, for products of segment
   socles. Applied to this datum, it makes the induced representation
   irreducible.
4. The published `ofCuspidalsInducedIso` identifies that induced
   representation with `cuspidalProductInduced`. The latter equals
   `unitaryBlock F w` by `rfl`, and irreducibility transports along the
   resulting equivalence.

`unitaryBlock_isTempered` (same hypotheses):

1. Each rank-one factor is irreducible, admissible and tempered: tempered
   because it is square-integrable.
2. Their block tensor on the torus Levi of `BlockShape.singletons m` is irreducible. This
   is `FiniteTensor.isIrreducible_external`, with Schur's lemma
   `admissibleSchur_scalarEndomorphism` for the factors.
3. The block tensor is tempered modulo the Levi center for a Borel Haar
   measure `μ`, supplied by `exists_isHaarMeasure_leviCentralQuotient`. This
   is the published `glBlockTensorTempered`.
4. The published `glTemperedInductionPreservation` then makes normalized
   parabolic induction of this tensor analytically tempered. That induction
   is definitionally the representation of `unitaryBlock F w`.

No irreducibility, temperedness, admissibility or linkage hypothesis is
assumed beyond the norm-one condition on the uniformizer values.
