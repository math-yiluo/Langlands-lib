# A reordered cuspidal tensor in the opposite Jacquet module of a product

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiGeometric`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`). It applies the whole-Levi
piece of the geometric lemma of Bernstein–Zelevinsky, through the published
`glGeometricPieceLifting`.

- `isSubquotient_of_injective`: the source of an injective intertwiner is a subquotient
  of its target, in the sense of `WeylBranchPieces.IsSubquotient`.
- `fineTwist_zero_zero`: the fine twist with zero parameters is the pullback along the
  inverse of `flattenedLeviEquiv`.
- `geometricPiece`: the setting is
  - an outer shape `B` with refinement `S` and `P = B.flatten S`;
  - supercuspidal representations `Y` on the blocks of `P`;
  - irreducible admissible `π i` that are quotients of `Ind_{S i}(Y⟨i,·⟩)`;
  - a permutation `e` of the blocks of `P` for which `P.blockPermutation e` is a
    minimal representative of `B` against `P.permute e`.

  Then the block tensor of the `Y` in the order `e` is a subquotient of the opposite
  Jacquet module, along `P.permute e`, of the normalized product of the `π i`.

  Proof. The fine tensor `ω` of the `Y` is irreducible and cuspidal (`glCuspidalTensor`),
  so its pullback `σ` to the refined Levi is irreducible and admissible
  (`fineTwistIrreducibleAdmissible`). Inner induction of `σ` is the block tensor of the
  `Ind_{S i}(Y⟨i,·⟩)` (`nonempty_innerInduced_flatten_equiv`), so it surjects onto
  `V = ⊠ π i`, which is irreducible and admissible. Refined normalized second
  adjointness (`normalizedSecondAdjointness`, second component) turns this surjection
  into a nonzero, hence injective, map `σ → innerJacquet V`. The geometric piece
  `glGeometricPieceLifting` makes the transported inner Jacquet module of `V` a
  subquotient of the opposite Jacquet module of `Ind_B V`. Finally
  `blockPermutationTensorEquiv` identifies the transported tensor with the reordered
  block tensor.
- `isSubquotient_blockTensor_cast`: such subquotient statements move along an equality
  of shapes `C = C'`. The block tensors are written through labels into a common family
  `atom : Λ → SmoothRep`, with size equalities, and the labels correspond under the
  cast. Proof: substitute the equality.
