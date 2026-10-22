# Standard compact subgroup at the infinite places

This module constructs a concrete compact subgroup of the actual archimedean
matrix group. For a number field `K` and natural rank `n`, it is the product of
`O(n)` at real places and `U(n)` at complex places, embedded into matrices over
the archimedean completions by the existing mixed-coordinate equivalence. All
constructions also make sense for any field `K`; no finiteness assumption on its
infinite places is needed for these compactness results.

## Source and provenance

The motivating original source is A. Borel and H. Jacquet, “Automorphic forms and
automorphic representations,” in *Automorphic Forms, Representations and
L-Functions*, Proceedings of Symposia in Pure Mathematics 33, Part 1 (1979),
pp. 189–202. Section 1.1 (printed p. 189, PDF p. 184) fixes a maximal compact
subgroup; section 1.4 (printed p. 190, PDF p. 185) uses `O(2, ℝ)` for `GL₂`;
sections 4.1–4.2 (printed p. 194, PDF p. 189) use the archimedean product and a
maximal compact subgroup in the adelic definition. The registered source is
`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

This is derived infrastructure. The source motivates the compact-subgroup input;
it is not cited as containing this general-rank Lean construction or its proof.
The implementation builds the orthogonal/unitary product explicitly and proves
compactness directly. It does **not** prove that the subgroup is maximal compact.
That additional assertion remains necessary before using maximality-dependent
results from the source.

## Definitions and correspondence

All project declarations are in `Langlands.Global`.

- `isCompact_unitaryMatrix` and `compactSpace_unitaryMatrix` prove compactness of
  Mathlib's actual `Matrix.unitaryGroup (Fin n) 𝕜`, for any `RCLike 𝕜`. The topology
  is the existing entrywise topology. No alternative matrix norm is installed.
- `realMatrix_mem_unitary_iff` identifies membership over `ℝ` with
  `A * A.transpose = 1`, so the real factors are the orthogonal groups, not the
  determinant-one special orthogonal groups.
- `ArchimedeanCompactFactors K n` is the product of a real unitary matrix at each
  real infinite place and a complex unitary matrix at each complex infinite
  place. Complex conjugation and transpose are those of Mathlib's matrix star.
- `ArchimedeanCompactFactors.toArchimedeanGL` assembles those matrices entrywise
  into `ArchimedeanGL K n`. Its `(i,j)` entry is the pair of functions
  `(v ↦ p.1 v i j, v ↦ p.2 v i j)`. The inverse is assembled from the inverse of
  every factor. `toArchimedeanGL_apply` gives this formula, and
  `continuous_toArchimedeanGL` and `toArchimedeanGL_injective` give continuity and
  faithfulness of the multiplicative map.
- `ArchimedeanCompactFactors.toInfiniteAdelicGL` composes that map with the inverse
  of the published `archimedeanGLCoordinates K n`. Its target is
  `Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`, precisely
  the group abbreviated `InfiniteAdelicGL K n` for number fields.
  `coordinates_toInfiniteAdelicGL` identifies its mixed coordinates and
  `toInfiniteAdelicGL_injective` proves injectivity. The map is bundled as a
  continuous monoid homomorphism between groups.
- `standardInfiniteCompact K n` is the subgroup range of that concrete map.
  `isCompact_standardInfiniteCompact`, `isClosed_standardInfiniteCompact`, and
  `compactSpace_standardInfiniteCompact` establish its compactness and closedness
  in the original completion-based topology.
- `ArchimedeanGL.realMatrix` and `ArchimedeanGL.complexMatrix` extract the actual
  matrices at a real or complex place from mixed coordinates.
  `mem_standardInfiniteCompact_iff` says exactly that every extracted real and
  complex matrix belongs to the corresponding unitary group. Together with
  `realMatrix_mem_unitary_iff`, this is the usual orthogonal/unitary membership
  criterion.

The empty matrix case `n = 0` is included. No positivity of the rank, arbitrary
carrier, assumed compactness certificate, or chosen inverse matrix is an input.

## Implemented proofs

The unitary locus is closed by `isClosed_unitary`. Mathlib's
`entry_norm_bound_of_unitary` places every entry in the closed unit disk of `𝕜`.
`IsCompact.matrix` supplies compactness of the matrix product of those disks,
and a closed subset of this compact set is compact. This proof covers rank zero
without a separate branch. Product compactness then gives compactness of
`ArchimedeanCompactFactors`.

Assembly preserves multiplication because taking the real or complex projection
commutes with the finite sum in matrix multiplication. The identity follows
entrywise. These facts construct actual matrix units from a factor and its
group inverse. Continuity is proved for both the value and inverse matrix, as
required by the units topology, using continuous coordinate evaluations and
continuous inversion on the factor groups. Equality of assembled matrices
implies equality of every entry at every place, which proves injectivity.

The completion-coordinate map uses the previously proved continuous
multiplicative equivalence. Its range is compact as the continuous image of a
compact space. It is closed because the completion product, hence its matrix
unit group, is Hausdorff. The membership converse packages each extracted matrix
with its unitary proof and verifies that assembling these factors recovers the
original matrix.

## Scope

This pair supplies a concrete subgroup and its structural facts. Maximal
compactness, conjugacy of maximal compact subgroups, center finiteness, growth,
cuspidality and automorphic representation constructions are separate work. The
existing subgroup-finite function construction can take this subgroup directly;
this module makes no additional claim of stability under all infinite-adelic
translations.
