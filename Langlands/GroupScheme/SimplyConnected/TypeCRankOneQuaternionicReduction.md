# Extracting the quaternionic rank-one model from type-C classification

Authors: Worker 178, Worker 64.

`Langlands.GroupScheme.typeCRankOneQuaternionic_of_typeCDivisionForm.{u}`
proves that the explicit premise `TypeCDivisionFormStatement.{u}` implies the
unchanged `TypeCRankOneQuaternionicStatement.{u}`. It does not prove the
classification premise or the unconditional target.

The proof extracts the actual Cartan numbering and distinguished-vertex
comparison from `HasRankOneCIndex n`. Its small-rank condition gives `n ≥ 2`,
so the general classification applies to that numbering. Consider the vertex
numbered 2. It is distinguished. The classification expresses its number as
`j * degree`, where `1 ≤ j ≤ splitRank G = 1`. Hence `j = 1` and
`degree = 2`. The degree formula `m * degree = 2 * n` now gives `m = n`.
Substituting these two equalities yields `dim_K D = 4` and symmetric
subspace dimension 3. The same involution, matrix, nonzero-size witness and
scheme isomorphism give the conclusion; the Witt index follows by rewriting
the supplied split rank. The star-triviality condition is unused because
the general type-C classification already starts from the full Cartan type.

This is an internal arithmetic extraction from the explicit classification
premise and the published actual-index predicate. It constructs no new group
model independently, uses no local arithmetic, and invokes no downstream local
classification or Kneser–Tits theorem. All fields and universe parameters are
retained, including characteristic two and the actual group-scheme isomorphism.
