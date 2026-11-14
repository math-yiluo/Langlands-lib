# Split-unipotent kernels of root maps induced by unipotent quotients

Author: Worker 407.

This internal supporting module extends
[RootSmoothQuotient](RootSmoothQuotient.md). It is used to build the kernel
part of `IntegralRootSpecializationData` in
`Langlands.BruhatTits.IntegralModels.RootSpecializationConstruction`.
All declarations are at arbitrary universe `u`.

## Setting

Work over an arbitrary field `k`. There is a homomorphism `q : H ⟶ G` of
smooth affine group schemes, a commutative group scheme `S` with
`i : S ⟶ H`, and a character `a` of `S`. Let `j : U ⟶ H` and `l : V ⟶ G`
be all-test representatives of the intrinsic root functors
`RelativeRoot.subgroup i a` and `RelativeRoot.subgroup (i ≫ q) a`. Write
`p = rootMap i q a j l hj hl` for the published canonical factorization
`U ⟶ V` with `p ≫ l = j ≫ q`.

## Results

- `range_kernelι_rootMap`: on every test scheme, the range of the full
  kernel inclusion of `p` is the inverse image under `j` of the range of
  the full kernel inclusion of `q`. The proof uses the published identity
  `range_kernelι_comp_mono` (composing with the monomorphism `l` does not
  change the kernel), the factorization `rootMap_comp`, and
  `range_kernelι_comp_eq_comap`. This part holds over any base scheme and
  needs no smoothness.

- `rootMap_kernel_isSplitUnipotent`: assume that `S` is a split torus, that
  `a ≠ 0`, and that the full kernel of `q` is represented on every test by a
  closed subgroup `n : N ⟶ H`. Assume also that `N` is smooth and connected
  and that the range of `n` is normal. Then the full scheme-theoretic kernel
  of `p` is unipotent and split unipotent (`RelativeRoot.IsSplitUnipotent`,
  the published finite `Ga`-series predicate). No smoothness or
  surjectivity of `q` is needed here.

  The proof is as follows. Conjugation by `i` preserves the normal subgroup
  `range n`, so `AutomorphicAction.onRepresentedSubgroup` gives an actual
  action `c` of `S` on `N`. The inclusion `n` intertwines `c` with
  conjugation by `i`. Let `A` be the positive cyclic semigroup
  `cyclicTail a 1`. The published intersection part of
  `RelativeRoot.semigroupComparison` (CGP 3.3.10, normal case) shows that
  the inverse image under `n` of the semigroup subgroup of `H` for `A` is
  the semigroup subgroup of `N` for `A` and `c`. The published
  `weightFiltration_one_eq_subgroup` identifies that ambient semigroup
  subgroup with the root functor of `i` and `a`. The composite
  `kernelι p ≫ j` lands in `range n` by the first result, so it factors as
  `e : kernel p ⟶ N` with `e ≫ n = kernelι p ≫ j`. The map `e` is a
  monomorphism. Its range is the semigroup subgroup of `N`. For the reverse
  containment, a test point `y` of `N` with `y ≫ n = x ≫ j` lies in the
  kernel of `p` by the first result, and the two factorizations agree after
  cancelling the monomorphism `n`. Thus `e` represents the semigroup
  subgroup of `N` for a semigroup not containing `0`. The published
  `RelativeRoot.semigroupRealization` (CGP 3.3.6) states that every such
  representative is unipotent and split unipotent.

- `rootMap_isFppfQuotient`: if `S` is split, `a ≠ 0`, and `q` is smooth and
  surjective as a scheme map, then `p` is the represented fppf quotient
  (`RelativeRoot.IsFppfQuotient`) by the range of its own full kernel
  inclusion. The published `rootMap_smooth_surjective` shows that `p` is
  smooth and surjective. Smoothness gives flatness and local finite
  presentation, and the kernel condition holds by definition.

- `rootMap_kernel_smooth`: under the same hypotheses, the full kernel of
  `p` is smooth. It is the pullback of the smooth map `p` along the unit
  section, as in the published `smooth_kernel_comp`.

- `kernelι_rootMap_isClosedSubgroup`: when `V` is affine, the full kernel
  inclusion of `p` is a closed immersion (`IsClosedSubgroup`).

## Provenance and scope

These results are internal consequences of the named published
constructions and theorems. They make no additional literature claim. The
role of the kernel is the one in the proof of Kaletha–Prasad, Proposition
9.4.25, where a smooth root model's special fibre maps onto a residue root
group with a split unipotent kernel. The module does not decide which
characters survive as roots of a quotient, and it says nothing about
building points or valuations.
