# Identifying special heads through decreasing induction

This internal helper applies the published individual-segment special
constituent existence theorem to a strong special head supplied by a caller.
It preserves an arbitrary prime, the actual p-adic field, its supplied
topological data, independent field and original carrier universes, and
saturated induced carriers.

`IsIrreducibleSocle.of_targetEquiv` transports a strong socle through an
equivalence of its constituent. The embedding is precomposed with the inverse
equivalence, so its image is unchanged. The proof retains the equality of
images of all irreducible embeddings.
`IsIrreducibleSocle.nonempty_equiv_of_subrepresentation` compares any
irreducible embedding with the strong socle through the actual canonical
socle representation.

`IsSegmentHead.isIrreducibleSocle_down` proves that any supplied strong head
of an increasing segment induction is the strong socle of every decreasing
induction representing the same segment. The published
`segmentSpecialConstituentExistence` supplies one representation with both
properties. Expressing its strong head relation and the caller's strong head
relation using the same actual representative identifies both with the
canonical head. Transporting the strong decreasing socle along the resulting
equivalence proves the conclusion.
`IsSegmentHead.decreasingSocleEmbedding` chooses the resulting actual
injective intertwiner and retains injectivity in a subtype.

`IsSegmentHead.nonempty_equiv_of_down_subrepresentation` identifies every
actual irreducible subrepresentation of that decreasing induction with the
supplied special head.
`IsSegmentHead.nonempty_equiv_of_down_jacquet_hom` gives a sufficient
Jacquet criterion: a nonzero actual map from the upper normalized Jacquet
module of an irreducible smooth representation to the decreasing inducing
tensor. Normalized first adjointness transports that nonzero map to a nonzero
map into the decreasing induction. Irreducibility makes the map injective,
and the preceding socle identification gives the actual equivalence.

This criterion assumes the actual nonzero Jacquet map as displayed. It does
not construct an Aubert image or prove any full segment Jacquet formula or
segment exchange identity.

The substantial imported project inputs are:

- `Classification.CanonicalConstituents`, for actual canonical heads and
  socles and comparison with every supplied strong head or socle.
- `Classification.SegmentSpecialConstituentExistenceProof`, for the
  unconditional individual-segment special head and decreasing strong socle.
  Its proof uses a common-image multiplicity-one criterion, actual cuspidal
  Jacquet factor counts, exactness and quotient/subobject detection,
  associated-induction intertwiners, and admissibility. It retains the
  actual strong kernel and image uniqueness clauses. It does not use
  multisegment exhaustion or the excluded analytic classifications.
- `Parabolic.NaturalFirstAdjointness`, for the actual normalized
  Hom-space linear equivalence. It uses upper block parabolics, positive
  half-modulus covariance for induction, inverse half-modulus for Jacquet
  modules, and right translation.

The provenance is an internal deduction from these published results and
Mathlib's fact that a nonzero map from an irreducible representation is
injective. No new assertion from the original literature is transcribed.

The recursive import closure at Library base
`8c5ba55d80ead022f06e4c04ae7621d1f734bac3` contains 651 project modules.
All imported Lean and Markdown pairs match the published base. The closure
contains lower smooth category, composition-series, tensor, induction,
Jacquet, cuspidal support, compact coefficient and adjointness constructions.
It also contains the general analytic predicates `Essential`, `Tempered`,
their opposite-support and unitary-dual adapters, and the proposition
definitions `TemperedSupportStatement` and `TemperedInductionStatement`.
Those proposition definitions supply no theorem conclusions here. The
closure contains no proof of the excluded multisegment, ordered-head,
quotient-coverage, tempered-block, square-integrable, or regular
classification conclusions. The identification uses neither full segment
Jacquet equivalence nor Aubert irreducible preservation.

Author: Worker 1186.
