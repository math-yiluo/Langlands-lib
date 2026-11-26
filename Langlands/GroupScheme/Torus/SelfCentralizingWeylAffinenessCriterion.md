# The affineness criterion for the Weyl quotient of a self-centralizing torus

This module proves the last conjunct of
[`SelfCentralizingTorusWeylAffinenessStatement`](SelfCentralizingWeylAffinenessStatement.md):
`G` is affine over `S` if and only if the Weyl quotient `W` is. It proves the
conjunct for *any* normalizer `n : N ⟶ G` and any quotient map `q : N ⟶ W`
that satisfy the statement's existence conditions; it does not construct `N`
or `W` (the module [`SeparatedWeylQuotient`](SeparatedWeylQuotient.md) does).
The direction "`W` affine implies `G` affine" takes the proposition
[`SelfCentralizingTorusConjugacyQuotientAffineStatement`](SelfCentralizingConjugacyQuotientStatement.md)
as a hypothesis. That proposition says that `G / N_G(T)` exists as a scheme
affine over `S` (SGA 3, Exposé XVI, Theorem 4.1(c), with Exposé XII,
Theorem 7.1(b)). The other direction uses no hypothesis beyond the data.

The mathematical route is the one in the proof of SGA 3, Exposé XVI,
Theorem 4.1(d), (iii) ⇔ (iv): `G` affine ⇒ `N` affine ⇒ `W = N/T` affine
(Exposé IX, 2.3), and back `W` affine ⇒ `N` affine ⇒ `G` affine, by descent
of affineness along the torsors `N → W` and `G → G/N` (Exposé VI_B, §9). All
results below are derived from Library results.

## Descent along a coset projection

`isAffineHom_of_coset_fibres`: let `i : H ⟶ G` be a monomorphism of group
schemes with `H` affine over `S`, and let `p : G.X ⟶ Y` be flat, surjective and
locally of finite presentation over `S`. Suppose that on every test scheme two
points of `G` have the same image under `p` exactly when they differ by a point
of `H`. Then `p` is an affine morphism. The lemma
`QuotientCell.multiplication_isPullback` shows that `G × H` is the fibre product
`G ×_Y G` through the maps `(g, h) ↦ g·h` and `(g, h) ↦ g`. The first projection
`G × H → G` is a base change of `H → S`, so it is affine. Affineness descends
along the fppf cover `p` (`MorphismProperty.of_isPullback_of_descendsAlong`).
No quasi-compactness of `p` is needed.

## The torus inside its normalizer

Fix `n : N ⟶ G` representing the normalizer functor `torusNormalizer t`.

- `torusToNormalizer hn : T ⟶ N` is the factorization of `t` through `n`, since
  every subgroup normalizes itself (`torusToNormalizer_comp`,
  `torusToNormalizer_hom_comp`). `mono_normalizer` records that `n` is a
  monomorphism.
- `mem_range_torusToNormalizer_iff`: a point of `N` comes from `T` exactly when
  its image in `G` comes from `T`. This uses that `n` is a monomorphism.
- `range_torusToNormalizer_isNormal`: the torus is a normal subgroup functor of
  `N`. Points of `N` normalize the torus in `G`, so they conjugate points of the
  torus to points of the torus.
- `isClosedSubgroup_torusToNormalizer`: if `t` and `n` are closed immersions,
  so is the factorization, because closed immersions cancel on the left.

Now take `q : N ⟶ W` with the kernel condition of the target statement: a point
`y` of `N` maps to `1` in `W` exactly when its image in `G` comes from `T`.

- `range_kernelι_eq`: the actual scheme kernel of `q` and the torus have the
  same points.
- `isFppfQuotient`: if `q` is in addition flat, surjective and locally of finite
  presentation, then `q` is a `RelativeRoot.IsFppfQuotient` by the torus.

## The four implications

- `isAffineHom_normalizer_of_weyl` (`W` affine ⇒ `N` affine). A relative torus
  is of multiplicative type, hence affine over `S`. The quotient map `q` has the
  affine kernel `T`, so it is affine by
  `RelativeRoot.IsFppfQuotient.isAffineHom_of_kernel`. The structure map of `N`
  is `q` followed by the structure map of `W`.
- `isAffineHom_weyl_of_normalizer` (`N` affine ⇒ `W` affine). The torus is a
  closed normal subgroup of multiplicative type in the affine group `N`. The
  theorem `NormalQuotient.exists_affine_fppfQuotient_of_multiplicativeType`
  constructs an fppf quotient `Q` of `N` by it with `Q` affine over `S`. That
  theorem takes a quotient statement as a hypothesis, which the theorem
  `affineDiagonalizableModelQuotient` discharges through
  `affineDiagonalizableNormalQuotient_of_model`. Two fppf quotients by the same
  subgroup functor are isomorphic, so affineness passes from `Q` to `W`
  (`FppfQuotientComparison.isAffineHom_target`).
- `isAffineHom_normalizer_of_group` (`G` affine ⇒ `N` affine). `n` is a closed
  immersion, hence affine.
- `isAffineHom_group_of_normalizer` (`N` affine and `G/N` affine ⇒ `G` affine).
  Let `p : G.X ⟶ Y` be flat, surjective and locally of finite presentation, with
  `Y` affine over `S`, whose fibres on test schemes are the cosets of the
  normalizer. Since `n` represents the normalizer, these are the cosets of `N`.
  The descent lemma above makes `p` affine, so `G → S`, which is `p` followed by
  `Y → S`, is affine.

## The criterion

`isAffineHom_iff` takes the hypothesis
`hS2 : SelfCentralizingTorusConjugacyQuotientAffineStatement.{u}`. It also takes
all hypotheses of the target statement on `G`, `T` and `t`, and data `N`, `n`,
`W`, `q` with `n` a closed subgroup representing `torusNormalizer t`, `q` flat,
surjective and locally of finite presentation, and the kernel condition. It
concludes `IsAffineHom G.X.hom ↔ IsAffineHom W.X.hom`. The forward direction
chains `isAffineHom_normalizer_of_group` and `isAffineHom_weyl_of_normalizer`.
The backward direction chains `isAffineHom_normalizer_of_weyl` with
`isAffineHom_group_of_normalizer`, applied to the map `p` that `hS2` provides
for `G` and `t`.

The smoothness of `N` and the separatedness, quasi-compactness and étaleness of
`W` are not used here. The hypotheses on `G` and on maximality and
self-centralization of `t` are used only to apply `hS2`.
