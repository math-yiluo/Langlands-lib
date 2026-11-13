# Roots of the derived subgroup of a split-torus centralizer

Author: Worker 146 (Task 5619).

This module proves one theorem, `Langlands.GroupScheme.exists_derivedCentralizerRootEquiv`.
It is used over the separable closure in
[`TitsKernelIndexData`](TitsKernelIndexData.md). Its provenance is internal: it
composes published Library constructions, named below, and assumes no unproved
statement.

## Statement

Work over an arbitrary field `F`. The data are:

- `G` and `D` with affine, locally-finite-type structure morphisms, and a group
  `M`;
- a split torus `a : A ⟶ G` (`IsSplitTorus A`), and `j : M ⟶ G` with
  `(torusCentralizer a).IsRepresentedBy j`, where `M` is connected reductive;
- a split torus `t : T ⟶ G` with an actual root datum `P` (index `J`,
  `IsRootDatumOf t P`), a maximal torus `tM : T ⟶ M` with `tM ≫ j = t`, and
  `f : A ⟶ T` with `groupHom f ≫ t = a`;
- an actual derived subgroup `i : D ⟶ M`, a split maximal torus `tD : TD ⟶ D`,
  and `τ : TD ⟶ T` with `tD ≫ i = groupHom τ ≫ tM`;
- an actual root datum `Q` of `tD` (index `K`).

The conclusion is an equivalence `φ : K ≃ {p : J // f ≫ P.root p = 0}` such
that, for every `q`, `Q.root q = τ ≫ P.root (φ q)` and
`Q.coroot q ≫ τ = P.coroot (φ q)`. The roots of `D` are the actual restrictions
along `τ` of the roots of `G` that vanish on `A`. The coroots of `D` push forward
along `τ` to the matching coroots of `G`.

## Proof

1. `t` is closed, as the composite of the closed subgroups `tM` and `j`. The
   latter is closed by `IsSplitTorus.isClosedSubgroup_torusCentralizer`. So the
   full Weyl image of `t` is finite (`splitTorusWeylImageFinite`).
2. The published `rootDatumExistence` gives an actual root datum `R` of `tM`.
3. The published `relativeRoots_splitTorusCentralizer_factor`
   ([`SimplyConnected/SplitTorusCentralizerRootModel`](../SimplyConnected/SplitTorusCentralizerRootModel.md))
   identifies the roots of `tM` with the roots `α` of `t` with `f ≫ α = 0`. In
   particular the roots of `tM` are roots of `t`. So
   `IsRootDatumOf.sameTorusSubgroupEmbedding`
   ([`Reductive/RootDatumSubgroupCoroots`](RootDatumSubgroupCoroots.md))
   embeds the indices of `R` into `J`, matching roots and coroots. By
   `SameTorusRootDatumEmbedding.range_index_eq`, its range is exactly
   `{p | f ≫ P.root p = 0}`.
4. `derivedTorusCentralComplement`
   ([`Rational/DerivedTorusCentralComplement`](../Rational/DerivedTorusCentralComplement.md))
   supplies an actual central split torus of `M` with a flat surjective product
   map. Its maximal split torus inputs come from `IsMaximalTorus.isMaximalSplitTorus`.
   `IsRootDatumOf.derivedRootDatumHom`
   ([`Rational/DerivedRootDatumComparison`](../Rational/DerivedRootDatumComparison.md))
   is then a morphism of root data from `R` to `Q`. Its weight map is
   `α ↦ τ ≫ α`, its coweight map is `ν ↦ ν ≫ τ`, and its index map is an
   equivalence.
5. `φ` is the inverse of this index equivalence, followed by the index
   embedding of step 3 and the identification of its range. The root and
   coroot laws are `root_weightMap_apply` and `coroot_coweightMap_apply` of the
   morphism, combined with the root and coroot equalities of the embedding.
