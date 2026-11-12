# Quaternionic symplectic groups of rank one over local fields

Author: Worker 118.

`Langlands.GroupScheme.Quaternionic.localSymplecticRankOne` proves exactly
`Langlands.GroupScheme.Quaternionic.LocalSymplecticRankOneStatement.{u}`
at arbitrary universe `u`. For a nonarchimedean local field `K`, a central
division `K`-algebra `D` of dimension four and a first-kind involution `σ`
whose symmetric subspace has dimension three, it applies to every
nondegenerate trace-valued `σ`-antihermitian form of rank two or three and
Witt index one. Its actual reduced-norm-one isometry group
`σ.symplecticGroup H` is simply connected, almost simple over `K`, and has
split rank one. Every hypothesis of the published statement is retained;
there is no characteristic restriction.

The proof composes the following Library results:

- `Langlands.LocalField.infinite_of_isNonarchimedeanLocalField` supplies the
  local `Infinite K` instance required by the split-rank calculation.
- `FirstKindInvolution.nonempty_algebraicModel` from
  `SymplecticMatrix.StandardComparison` supplies a finite Galois extension
  and an actual isomorphism of the base-changed quaternionic group with the
  standard symplectic group of size `card (Fin m) = m`.
- `Symplectic.structureStatement` from `Symplectic.StructureProof` proves
  simple connectedness and absolute almost simplicity of the standard group
  over every field, for every size at least two. The alternatives `m = 2`
  and `m = 3` give this size bound.
- `Symplectic.AlgebraicModel.isSimplyConnected_and_isAlmostSimple` uses the
  standard structure theorem and this bound to transport the structural
  properties along the actual model isomorphism and descend them to the
  original group. Its simple-connectedness argument reflects along the
  algebraic extension; its almost-simplicity argument reflects absolute
  almost simplicity along the field extension and then takes almost
  simplicity over `K`.
- `FirstKindInvolution.splitRank_symplecticGroup_eq_one_of_wittIndex_eq_one`
  from `Quaternionic.SymplecticSplitRank` supplies the rank equality for
  the original form. That result combines a nonzero cocharacter obtained
  from a hyperbolic basis with the Witt-index upper bound.

The three conclusions are assembled for the same group scheme
`σ.symplecticGroup H`. This is an internal composition of the named published
results, with no additional structural premise or source assertion.
