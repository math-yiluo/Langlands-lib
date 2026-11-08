# The modified product `N''` is a closed immersion

This module proves the `N''` half of Steinberg's Lemma 9.13 (1965) for the published
supplied-data morphism `SplitPinning.steinbergModifiedProduct` of
`Rational.SteinbergModifiedRootProduct`. It shows that this morphism from affine
`(q + 1)`-space to `G` is a closed immersion of schemes. It is an internal prerequisite for
the even type `A` case of the quasi-split Steinberg quotient task. There `N''` is the
substitute cross-section on the stratum `f = 0`.

## Setting

All results are in `Langlands.GroupScheme.SplitPinning`. They use an arbitrary field `k`,
an actual affine group scheme `G` over `Spec k` and a supplied split pinning `p`. The data
are as follows:

- `D : p.SteinbergModifiedData`: distinct simple roots `a`, `b`, a root `alpha` with
  `root alpha = root a + root b`, an arbitrary root map `D.xAlpha` and an arbitrary
  reflection representative `D.nAlpha` of `alpha`;
- an ordering `e : Fin q ≃ D.Complement` of the remaining simple roots;
- normalized simple-root maps `x`;
- arbitrary simple reflection representatives `n`.

No type `A` hypothesis and no normalization of the representatives is assumed.

## Definitions

- `RootParametrization.conjugateHom x m` is a root map `x` of an arbitrary root followed by
  inner conjugation by a normalizer point `m`. It is the analogue for arbitrary roots of the
  published `NormalizedRootParametrization.conjugateHom` of `Rational.SteinbergPrefixWeights`.
- `ReflectionRepresentative.normalizerPoint` is a supplied reflection representative as an
  element of the subgroup `normalizerPoints p.inclusion`.
- `modifiedRoots D e : Fin (q + 1) → p.rootIndex` is `alpha` followed by the roots `e j`.
  `modifiedRootMaps D e x` is `D.xAlpha` followed by the maps `x (e j)`.
  `modifiedNormalizers D e n` is `D.nAlpha` followed by the representatives `n (e j)`.
  These are the factors of `N''` in Steinberg's order `X_α σ_α ∏_j (X_j σ_j)`.
- `modifiedPrefixRootHom D e x n j` is the `j`-th root map conjugated by the ordered product
  of the representatives before it, written with the published `orderedPrefix`.
  `modifiedPrefixWeight D e n j` is the Weyl transform of its root by that product.
- `modifiedCoxeterNormalizer D e n` is the ordered product of all representatives of `N''`.

## Results

- `RootParametrization.isClosedSubgroup_conjugateHom`,
  `RootParametrization.scalarPoint_conjugateHom` and
  `RootParametrization.conjugateHom_torus_equivariant`: a conjugated root map is a closed
  subgroup. On every test its value at `c` is `m x(c) m⁻¹`. It is torus-equivariant for the
  Weyl transform `weylAction p.inclusion m (root α)`.
- `ReflectionRepresentative.weylAction_normalizerPoint`: a reflection representative of `α`
  acts on characters by the reflection of `α`. `weylAction_modifiedNormalizers` applies this
  to the factors of `N''`.
- `modifiedPrefixWeight_eq`: each prefix weight is the ordered prefix of the reflections of
  the modified roots, applied to the next modified root.
- `modifiedRoots_linearIndependent`: the roots `root a + root b` and `root (e j)` are
  linearly independent over `ℤ`.
- `modifiedPrefixWeight_linearIndependent`: the prefix weights are linearly independent over
  `ℤ`.
- `isClosedSubgroup_modifiedPrefixRootHom` and `modifiedPrefixRootHom_torus_equivariant`:
  the hypotheses of the independent-weight product theorem for the prefix maps.
- `steinbergModifiedProductPoint_eq_independentWeightProduct`: on every test `T` and for all
  global functions `s` and `d`, the point formula of `N''` equals the independent-weight
  product of the prefix maps at `Fin.cons s d`, times the constant point of
  `modifiedCoxeterNormalizer`.
- `steinbergModifiedProduct_eq_independentWeightProduct`: as morphisms,
  `steinbergModifiedProduct D e x n` equals the published `IndependentWeightProduct.morphism`
  of the prefix maps followed by `G.rightTranslation (modifiedCoxeterNormalizer D e n)`.
- `isClosedImmersion_steinbergModifiedProduct`: the underlying scheme morphism
  `(steinbergModifiedProduct D e x n).left` is a closed immersion.

## Proof as implemented

The proof follows the published split reduction `Rational.SteinbergIndependentWeightReduction`.
It replaces the full simple system with the modified roots.

**Conjugated root maps.** Conjugation by a normalizer point `m` composes with the published
`G.innerIso m`. The scalar formula is `comp_innerIso_hom`. For torus equivariance, write
`t' = t ∘ σ⁻¹`, where `σ` is the normalizing automorphism of `m`. Then `m⁻¹ t m = t'`, so the
torus law of `x` at `t'` gives the law for the Weyl transform, by definition of
`weylAction`. A reflection representative of `α` has, by uniqueness of the normalizing
automorphism (`IsNormalizingPoint.unique`), the character action fixed in its
`characterAut_eq` field, namely the reflection of `α`.

**Independence.** Mathlib's `LinearIndependent.finCons'` reduces independence of the
modified roots to two facts. The roots `root (e j)` are independent, as a subfamily of the
simple roots (`RootPairing.Base.linearIndepOn_root`). If `c (root a + root b) + y = 0` with
`y` in their span, then `c • root a = -(c • root b + y)`. This lies in the span of the simple
roots other than `a`, so Mathlib's `LinearIndependent.eq_zero_of_smul_mem_span` gives
`c = 0`. The published `orderedReflectionWeights_linearIndependent` then transfers
independence to the prefix weights, through `modifiedPrefixWeight_eq` and the reflection
formula `RootPairing.reflection_apply`.

**Moving the representatives.** On a test, the factors `x_j(c_j) n_j` of `N''` are the
images under the constant-point homomorphism of the representatives. The published
`interleaved_prod_eq_prefix_conjugates` rewrites the ordered product as the product of the
prefix conjugates `P_j x_j(c_j) P_j⁻¹` followed by the product of all representatives. Here
`P_j` is the ordered prefix, and `map_orderedPrefix` commutes it with the homomorphism. The
morphism identity follows from `comp_rightTranslation` and `Fin.cons_self_tail` for the
coordinates of the universal point.

**Closed immersion.** The published `independentWeightProductImmersion` (the Library's
proof of `IndependentWeightProductImmersionStatement`) makes the product of the prefix maps
a closed immersion. Right translation by a rational point is an isomorphism
(`rightTranslationIso`), and a closed immersion followed by an isomorphism is a closed
immersion.

## Provenance and scope

The source is Robert Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
Lemma 9.13 (printed p.75, PDF p.28):

> The sets N'' and N''' are closed and irreducible in G. The natural maps from the Cartesian
> products X_α × Π X_j and X_α × T_α × Π X_j to N'' and N''', respectively, are isomorphisms
> of varieties.

Steinberg deduces the `N''` part from 7.1 and from Lemma 9.12, which says that the modified
roots form a simple system of type `A_{2m-1}`. The Lean proof uses instead only the linear
independence of the modified roots. So it holds for arbitrary supplied modified data, outside
type `A` and with arbitrary representatives. In scheme language, a closed immersion is
Steinberg's statement that `N''` is closed and that its parametrization is an isomorphism
onto it.

The module does not treat `N'''`, and it states no irreducibility. It does not identify the
image with the zero set of `f`. Steinberg's Corollary 9.19 and the remaining parts of Lemma
9.13 remain obligations of the host task.
