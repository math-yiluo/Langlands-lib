# Proof of the rational-point/matrix comparison of the GL operator

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.GL.RationalAlternatingOperatorComparisonStatement`
(module `GeneralLinearRationalComparisonStatement`) at universes `u`, `v`:

`theorem rationalAlternatingOperatorComparison : RationalAlternatingOperatorComparisonStatement.{u, v}`.

The statement and its provenance (derived from Aubert 1995,
`aubert-1995-duality`, Définition 1.5, printed p. 2181) are described in the
statement module's Markdown. This file describes the Lean proof only. It
uses no assumptions beyond the statement's quantified data.

## Membership lemmas

In namespace `Langlands.Aubert.General.RationalPointFamily.GL`, for a field `k`
and a strictly decreasing cocharacter `ν` of the diagonal torus `iD` of
`GL_N`:

- `leviRootSubsetEquiv_symm_edge` records, by `rfl`, that the block shape
  attached to a simple-root subset through the inverse edge equivalence is
  `(blockRootSubsetEquiv k ν hν).symm J`.
- `mem_parabolic_iff_block`, `mem_levi_iff_block` and
  `mem_unipotent_iff_block` say: a rational point `x` lies in the standard
  parabolic, Levi or unipotent subgroup at the
  simple-root subset `J` if and only if its image under
  `GroupScheme.GeneralLinear.rationalPointsEquiv` lies in the corresponding
  block subgroup of `GeneralLinear N k` for the block shape
  `(blockRootSubsetEquiv k ν hν).symm J`. Each is read off from the published
  subgroup equalities `parabolic_blockRootSubsetEquiv`,
  `levi_blockRootSubsetEquiv`, `unipotent_blockRootSubsetEquiv`
  (module `GeneralLinearRationalIndexing`), after writing `J` as the image of a
  block shape. The suffix `_block` keeps them distinct from the general
  `RationalPointFamily.mem_levi_iff` and `RationalPointFamily.mem_unipotent_iff`
  (module `StandardFamilyStructure`).

## Main proof

Fix `p`, `F`, `T`, `N`, `ν`, `hν`. The proof installs the field topology
`T.topology`, the topological-ring instance from `T.valuativeRel` and
`T.localField`, and `pointTopology` on the rational points. It sets
`e := rationalPointsContinuousMulEquiv N F.Carrier`, a continuous group
isomorphism onto `GeneralLinear N F.Carrier`. It also sets
`σ := (edgeSimpleRootEquiv F.Carrier ν hν).symm`, and `Bs J` for the block
shape attached to `J`.

1. **Topological group conditions.** The proof installs on
   `GeneralLinear N F.Carrier` the instances
   `T.generalLinearLocallyCompactSpace N`, `T.generalLinearNonarchimedean N`
   and, through `T.fieldT2` on the field, the Hausdorff property. On the
   rational points it installs the topological-group instance
   `rationalPoints_isTopologicalGroup`. Local compactness and the Hausdorff
   property then pull back along the closed embedding and the embedding
   underlying the homeomorphism `e`. Nonarchimedeanity comes from
   `NonarchimedeanGroup.nonarchimedean_of_emb` applied to the group
   homomorphism `e.symm`, an open embedding of the nonarchimedean group
   `GeneralLinear N F.Carrier` onto the rational points (this lemma needs the
   topological-group instance on the target). All three are proved, not
   assumed.
2. **Premises are satisfiable.** Fix the instances and the structural data.
   The membership lemmas give the compatibilities `hPP`, `hMM`, `hUU` of every
   rational subgroup with its block subgroup under `e`.
   - The unipotent and parabolic subgroups are closed: they are preimages
     under `e` of the closed block subgroups (`isClosed_unipotentSubgroup`,
     `isClosed_parabolic`).
   - The Levi projection is continuous by
     `GroupTransport.continuous_projection_transport` (module
     `OperatorTransport`). It is applied to the block decomposition
     `generalSemidirectDecomposition`, whose projection is the composite of
     the continuous maps `leviProjectionContinuous` and `leviEquivContinuous`
     (`generalSemidirectDecomposition_projection`).
   - The limit-of-compact-subgroups property is the published
     `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
     with `standardCocharacter`.
   - Finite-length preservation of normalized induction and Jacquet
     restriction at carrier universe `max (u + 1) v` is transported by
     `inductionPreservesFiniteLength_transport` and
     `jacquetPreservesFiniteLength_transport` from the matrix group. There it is
     part of `Parabolic.generalLinearParabolicFiniteLength`, given the published
     modulus compatibility `Parabolic.generalLinearModulusCompatibility F T`.
3. **Operator equality.** For arbitrary premise proofs, the published
   `Aubert.generalAlternatingOperator_eq` (module
   `GeneralLinearSpecialization`, with the same modulus compatibility) rewrites
   `Aubert.alternatingOperator F T N` as the general unadjusted operator for
   the matrix block family indexed by `Finset (Fin (N - 1))` through
   `BlockShape.leviRootSubsetEquiv`. At `σ.finsetCongr J` that family is
   definitionally the block family of `Bs J` (`leviRootSubsetEquiv_symm_edge`),
   so `hPP`, `hMM`, `hUU` match the transport hypotheses. The simple
   relative roots get the `Fintype` instance `simpleRelativeRootFintype`. The
   remaining equation is exactly `GroupTransport.alternatingOperator_transport`
   (module `OperatorTransport`), with `e`, `σ` and `hPP`, `hMM`, `hUU`. Its
   operator-level premises are proof-irrelevant, so the proofs supplied by the
   statement are accepted.

`lean_check` reports the axioms `propext`, `Classical.choice`, `Quot.sound`.
