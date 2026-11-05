# Scalar base change of affine-chart Weil restriction

This is a derived construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp. 9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad uses compatibility of restriction of scalars with base change in
reducing the adelic comparison to finite extensions of complete fields.
This file implements the all-test representing equivalence for base
change of the existing actual affine-chart Weil restriction. Its detailed
pullback and adjunction construction is derived infrastructure for that
step. It proves no topological comparison.

The main declaration is
`affineChartWeilRestrictionScalarBaseChangeTestEquiv` in
`Langlands.AlgebraicGeometry.PointTopology`.

## Actual schemes and hypotheses

The rings `A`, `B` and `C` are arbitrary commutative rings in a common
universe `u`, with actual `A`-algebra structures on `B` and `C`.
The representing-equivalence construction assumes `Module.Finite A B`
and `Module.Projective A B`. No finiteness condition on `C`, field,
separability, characteristic, nonzero-rank or topology hypothesis occurs.

Write

```text
b = Spec.algebraMap A B,       c = Spec.algebraMap A C,
P = pullback c b,
pc = pullback.fst c b : P ⟶ Spec C,
pb = pullback.snd c b : P ⟶ Spec B.
```

These are the actual scheme pullback and its projections. The target
`Y : Over (Spec B)` has locally finite-type structure morphism. Set
`G = affineChartWeilRestriction A B Y`, the existing actual scheme over
`Spec A` glued from restrictions of affine opens of `Y.left`.
Let `Y_P = (Over.pullback pb).obj Y`, its actual pullback to `P`,
and `G_C = ringBaseChange A C G`, the actual pullback of `G` to `Spec C`.

For the general representing equivalence, `Y.hom` is separated and
`hY : HasFiniteAffineNeighborhoods Y.left`: every finite set of actual
points of `Y.left`, including the empty set, lies in an affine open.
The later projective-immersion specialization derives both conditions
from the displayed actual immersion. No geometric condition on `Y_P`
is assumed.

## Actual extension and test-pullback isomorphisms

`weilRestrictionScalarBaseChangeExtensionIso` identifies
`Over.mk pc` with `ringTest C (C ⊗[A] B)` over `Spec C`.
It uses Mathlib's `pullbackSpecIso A C B` and its first-projection
formula. Thus the actual extension pullback is canonically the spectrum
of the actual tensor-product algebra with its specified `C`-structure.
This declaration uses only the ring and algebra hypotheses.

For every actual test scheme `T : Over (Spec C)`,
`weilRestrictionScalarBaseChangeTestIso` constructs an isomorphism
over `Spec B`:

```text
(Over.map pb).obj ((Over.pullback pc).obj T)
  ≅ ringBaseChange A B ((Over.map c).obj T).
```

Its underlying morphism is Mathlib's actual pullback-pasting isomorphism
`pullbackRightPullbackFstIso c b T.hom`. The second-projection identity
makes it an isomorphism over the original extension spectrum. The theorem
`weilRestrictionScalarBaseChangeTestIso_natural` proves naturality in
every morphism of `C`-test schemes, using the two pullback projections
and `Over.pullback_map_left`. These constructions likewise need no
finiteness or target hypothesis.

## Canonical comparison and representing equivalence

`affineChartWeilRestrictionScalarBaseChangeComparison` sends each
actual morphism `p : T ⟶ G_C` to a morphism
`(Over.pullback pc).obj T ⟶ Y_P` over `P`.
First the pullback adjunction for `c` turns `p` into a morphism from
the same test scheme, regarded over `Spec A`, to `G`. The original
`affineChartWeilRestrictionComparison` applies actual base change and
the original glued counit. Precomposition with the preceding test
isomorphism pastes the source pullbacks. Finally the pullback adjunction
for `pb` lifts this map to the actual target `Y_P`.
The comparison needs the finite-projective and locally finite-type
hypotheses, but neither separatedness nor finite-set affine neighborhoods.

`affineChartWeilRestrictionScalarBaseChangeComparison_fst` records its
exact composite with the target projection to `Y.left`. It is the
original counit comparison after the test-pasting isomorphism.
`affineChartWeilRestrictionScalarBaseChangeComparison_natural` proves
that comparison of `f ≫ p` is pullback of `f` along `pc` followed by
comparison of `p`, for every morphism `f : T ⟶ S`.

Under the stated separatedness and finite-set neighborhood premises,
`affineChartWeilRestrictionScalarBaseChangeTestEquiv` gives

```text
(T ⟶ G_C) ≃ ((Over.pullback pc).obj T ⟶ Y_P)
```

for every actual `C`-test scheme `T`. Tests have no affineness,
finite-type, separatedness or quasi-compactness restriction.
The equivalence is the composition of the inverse pullback-adjunction
equivalence for `c`, the existing all-test representing equivalence for
`G`, precomposition with the test-pasting isomorphism, and the
pullback-adjunction equivalence for `pb`. Its inverse laws follow from
these actual equivalences. No representing property is assumed for
the pulled-back target.

The `_apply` theorem identifies its forward map with exactly the
canonical comparison above. The `_natural` theorem transfers comparison
naturality to the equivalence. The `_symm_natural` theorem proves that
the inverse of pullback of `f` followed by `q` is `f` followed by the
inverse of `q`; it applies injectivity of the forward equivalence and
the proved forward naturality.

## Actual projective-immersion specialization and retained scope

`projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv` replaces
the separatedness and finite-set neighborhood premises by a natural
number `n`, an actual locally closed immersion
`i : Y.left ⟶ ProjectiveSpace B n`, and the equality
`i ≫ projectiveSpaceToSpec B n = Y.hom`.
It uses the existing proved `isSeparated_of_projectiveImmersion` and
`hasFiniteAffineNeighborhoods_of_projectiveImmersion` to apply the
general equivalence. Its `_apply`, `_natural` and `_symm_natural`
theorems preserve the same canonical forward map and both naturalities.
The target remains locally finite type; no quasi-compactness is inferred
from an arbitrary projective immersion over an arbitrary ring.

This unit proves the all-test representing property of the actual
base-changed original scheme over the actual extension pullback.
It supplies the extension's tensor-spectrum isomorphism, but does not
yet transport the target and functor through it or identify `G_C`
with a separately constructed affine-chart Weil restriction over
`C` and `C ⊗[A] B`. Those identifications, all-upper-place tensor and
product decompositions, geometric preservation of the representing
scheme, arithmetic integral models, function-field completion
instances, the local topology compatibility of these comparisons,
and the global adelic comparison remain separate obligations of
Example 4.2 and the whole-paper task.
