# The local rank-one classification: proof

Author: Worker 84.

`Langlands.GroupScheme.localRankOneClassification.{u}` proves the
published proposition
`Langlands.GroupScheme.LocalRankOneClassificationStatement.{u}` as stated,
at every universe `u`, with no hypothesis. The statement is in the module
`Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationStatement`.

Fix a nonarchimedean local field `K` and an affine group scheme `G` over
`Spec K` that is simply connected and absolutely almost simple, with
`splitRank G = 1`. Then `G` is one of the following:

- (i) `SL₂(D)`, i.e. `CentralSimpleUnits.BinaryRoot.groupScheme K D`, for a
  finite-dimensional central division algebra `D`;
- (ii) `HermitianRoot.SchemeModel.groupScheme K L H w hw`, the special
  unitary group of a hermitian form of Witt index 1 in `m + 2 = 3` or `4`
  variables. Here `L` is a separable quadratic extension of `K`, and `H` is
  an anisotropic diagonal hermitian form on `Fin m` with `m = 1` or `2`
  whose weights are the units `w`;
- (iii) for a quaternion division algebra `D` with an involution `σ` of the
  first kind whose symmetric subspace has dimension 3, one of two groups.
  The first is the quaternionic symplectic group `σ.symplecticGroup H` of an
  invertible antihermitian `H` of size 2 or 3 with Witt index 1. The second
  is a spin cover `π : G ⟶ σ.isometryGroup q`, `σ.IsSpinCover q π`, of the
  isometry group of a nondegenerate `σ`-quadratic form `q` in 4 or 5
  variables with Witt index 1.

In (i), (ii) and the symplectic case `G` is isomorphic to the named group
scheme; in the spin case the conclusion is the morphism `π`. Every
characteristic of `K` and of its residue field, including 2, is covered.

## Implemented proof

The proof is a single term. It applies the published conditional theorem
`localRankOneClassification_of_indexStatements` from
`SimplyConnected.LocalRankOneClassificationIndexReduction` to seven
published, unconditional Library theorems. Those theorems prove its seven
hypotheses at the same universe `u`:

1. `titsIndexExistence : TitsIndexExistenceStatement.{u}`
   (`Reductive.TitsIndexExistenceProof`). Every semisimple affine group
   scheme of locally finite type over a field has actual Tits-index data.
2. `localRankOneTitsIndex : LocalRankOneTitsIndexStatement.{u}`
   (`SimplyConnected.LocalRankOneTitsIndexProof`). Over a nonarchimedean
   local field, the actual index of such a `G` is one of five:
   `¹A_(2d−1),1^(d)`, `²A_2,1^(1)` or `²A_3,1^(1)`, `C_2,1^(2)` or
   `C_3,1^(2)`, `²D_4,1^(2)`, or `¹D_5,1^(2)`.
3. `innerTypeANormOne : InnerTypeANormOneStatement.{u}`
   (`SimplyConnected.InnerTypeANormOneProof`).
4. `CentralSimpleUnits.matrixNormOneSplitRank :
   CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}`
   (`SimplyConnected.MatrixNormOneSplitRankProof`). With item 3, this is
   what the reduction's inner type `A` case needs to give family (i).
5. `outerTypeARankOneHermitian : OuterTypeARankOneHermitianStatement.{u}`
   (`SimplyConnected.OuterTypeARankOneHermitianProof`). Outer type `A`
   indices give family (ii).
6. `typeCRankOneQuaternionic : TypeCRankOneQuaternionicStatement.{u}`
   (`SimplyConnected.TypeCRankOneQuaternionicProof`). Type `C` indices
   give the symplectic part of family (iii).
7. The type `D` input `TypeDRankOneSpinStatement.{u}` is given by the
   term `typeDRankOneSpin_of_classicalTypeDSpinPresentation
   classicalTypeDSpinPresentation`. It applies the published conditional
   theorem in `SimplyConnected.TypeDRankOneSpinIndexReduction` to the
   published proof
   `classicalTypeDSpinPresentation : ClassicalTypeDSpinPresentationStatement.{u}`
   (`SimplyConnected.ClassicalTypeDSpinPresentationProof`). The indices
   `²D_4,1^(2)` and `¹D_5,1^(2)` give the spin part of family (iii).

The case split is done inside the imported reduction, whose Markdown
explains it. It starts by deriving `LocallyOfFiniteType G.X.hom` from
simple connectedness. It then gets index data from item 1 and splits on
the five alternatives of item 2. Each alternative is sent to one family
of the conclusion through items 3–7. Every witness is passed on unchanged;
the only computation is `n − 1 ∈ {1, 2}` in the outer type `A` case.

The theorem adds no premise: every input is a proved Library theorem. The
proof term uses no `LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement`,
`LocalRankOneKneserTitsStatement` or `LocalKneserTitsStatement`; each of
these is downstream of the classification. A development check of the
theorem reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

Internal composition of published results. The classification is
Prasad–Raghunathan, *On the Kneser–Tits problem* (Comment. Math. Helv. 60,
1985), §2, printed p. 111 / PDF p. 6. It is due to Kneser in
characteristic zero and to Bruhat–Tits in general. The Lean proof follows
the index-by-index route of the imported reduction, not the original
proofs. The paired Markdown of the seven input theorems explains their
proofs.
