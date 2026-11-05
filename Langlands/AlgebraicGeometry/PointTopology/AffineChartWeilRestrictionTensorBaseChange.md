# Tensor-algebra base change of the actual affine-chart Weil restriction

This is derived algebraic infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, December 31, 2011, Example 4.2,
printed pp. 9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
On p. 10 the source first identifies the base change of a Weil restriction
with restriction along the completed tensor algebra, then decomposes that
algebra and restriction over the places above the original place. This
module constructs the first identification as an isomorphism between actual
schemes, with its canonical map fixed on every test scheme. It builds on the
preceding scalar-base-change construction and the original proved all-test
representing equivalence.

The proof uses actual pullbacks, the tensor-spectrum isomorphism, and Yoneda.
It does not use an assumed representation of the new functor. Its
commutative-ring formulation is a proved generalization of this algebraic
step in Conrad's field setting, consistent with the finite locally free
ring-map scope noted on p. 9. The auxiliary preservation and naturality
lemmas are internal to this construction.

## Rings, schemes, and hypotheses

All rings and schemes have the common universe parameter `u`. Let `A`, `B`,
and `C` be arbitrary commutative rings, with specified `A`-algebra structures
on `B` and `C`. Set

```text
R  = C tensor_A B
c  : Spec C -> Spec A
b  : Spec B -> Spec A
P  = Spec C times_{Spec A} Spec B
pc : P -> Spec C
pb : P -> Spec B.
```

The `C`-algebra structure on `R` is the left tensor inclusion. The local
instance `Algebra.TensorProduct.rightAlgebra` supplies the `B`-algebra
structure through the right tensor inclusion. The map
`pullbackSpecIso A C B : P ≅ Spec R` respects both projections.

The original target is the actual object
`Y : Over (Spec (CommRingCat.of B))`. From the canonical comparison onward,
`B` is finite and projective as an `A`-module, and `Y.hom` is locally of
finite type. Write

```text
G  = affineChartWeilRestriction A B Y
GC = ringBaseChange A C G
YR = ringBaseChange B R Y
G' = affineChartWeilRestriction C R YR.
```

These are the existing glued representing construction and actual scheme
pullbacks. The `G'` construction is separately performed over the new rings;
it is not defined to be `GC`. The existing tensor-product instances prove
that `R` is finite projective over `C`.

The all-test equivalences and scheme isomorphism additionally require
`IsSeparated Y.hom` and
`hY : HasFiniteAffineNeighborhoods Y.left`. The latter predicate means that
every finite set of actual points of `Y.left` is contained in an actual
affine open. No new representation, affine-neighborhood condition, or
separatedness hypothesis on `YR` is an input. No topology, field,
characteristic, separability, positive-rank, quasi-compactness, or affine
test-scheme assumption is imposed. Local finite type is retained separately
from finite type.

## Geometry after base change

`hasFiniteAffineNeighborhoods_of_affine` proves that an affine morphism
`f : X -> Z` pulls the finite-set affine-neighborhood property back from
`Z` to `X`. For a finite subset `E` of `X`, the proof takes an affine open
containing the finite image `f(E)`, then takes its inverse image. An affine
morphism makes that actual inverse-image open affine.

`hasFiniteAffineNeighborhoods_ringBaseChange` applies this result to the
projection from an actual ring base change to the original scheme. That
projection is affine because it is the base change of a morphism between
affine ring spectra. Consequently `hY` supplies the corresponding condition
on `YR`. Local finite type and relative separatedness of `YR` follow from
their existing stability under base change. These facts justify applying the
original representing equivalence over `C` and `R`.

## Actual tensor-spectrum transport

For every actual `C`-test scheme `T`, the definitions
`weilRestrictionTensorBaseChangeTestIso` and
`weilRestrictionTensorBaseChangeTargetIso` construct isomorphisms over
`Spec R`:

```text
Over.map(e.hom)(pc^* T) ≅ ringBaseChange C R T
Over.map(e.hom)(pb^* Y) ≅ YR,
where e = pullbackSpecIso A C B.
```

Their underlying maps are actual `pullback.map` morphisms. The identity
maps on the original schemes and base, together with `e.hom`, make these
maps isomorphisms. The two projection identities of `pullbackSpecIso`
establish compatibility with the left and right tensor inclusions.

`weilRestrictionTensorBaseChangeTestIso_natural` proves naturality in `T`
by checking both pullback projections.
`weilRestrictionTensorBaseChangeTestIso_inv_natural` gives the corresponding
inverse formula by cancellation of the isomorphism.

## Canonical comparison and all-test representation

For `p : T -> GC`,
`affineChartWeilRestrictionTensorBaseChangeComparison` is the actual map

```text
ringBaseChange C R T
  --testIso.inv--> Over.map(e.hom)(pc^* T)
  --Over.map(e.hom)(scalarComparison(p))-->
                      Over.map(e.hom)(pb^* Y)
  --targetIso.hom--> YR.
```

Here `scalarComparison` is the preceding scalar-base-change comparison,
defined from the original glued counit. Thus this construction retains the
original canonical map through the specified actual pullback isomorphisms.
The comparison needs only the finite-projective and local-finite-type
hypotheses; separatedness and `hY` enter when proving it is a bijection.

`affineChartWeilRestrictionTensorBaseChangeTestEquiv` constructs

```text
Hom_C(T, GC) ≃ Hom_R(ringBaseChange C R T, YR).
```

It composes the proved scalar-base-change equivalence with the fully
faithful Hom equivalence of `Over.map(e.hom)` and `Iso.homCongr` for the
test and target isomorphisms. The `_apply` theorem identifies its forward
function with the canonical comparison just defined. For every actual
`f : T -> S`, the `_natural` theorem states

```text
E_T(f >> p) = (baseChange C R).map(f) >> E_S(p).
```

The same equation for the comparison is proved from scalar comparison
naturality and inverse test-isomorphism naturality. The
`_symm_natural` theorem proves inverse naturality by applying injectivity of
`E_T`, forward naturality, and the equivalence's inverse laws.

## Isomorphism with the separately glued Weil scheme

`affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv` composes the
last equivalence with the inverse of the original representing equivalence
for `G'`. The geometric hypotheses of that second equivalence have just
been derived. This gives, naturally for every actual test scheme,

```text
eta_T : Hom_C(T, GC) ≃ Hom_C(T, G').
```

`affineChartWeilRestrictionTensorBaseChangeHom` is
`eta_GC(identity)`. Naturality gives
`eta_T(p) = p >> affineChartWeilRestrictionTensorBaseChangeHom`, as proved
by `_RepresentingEquiv_eq_comp`. Since each `eta_T` is bijective, the proved
Yoneda criterion `isIso_of_yoneda_map_bijective` makes this one canonical
morphism an isomorphism. The definition
`affineChartWeilRestrictionTensorBaseChangeIso` packages it as

```text
ringBaseChange A C (affineChartWeilRestriction A B Y)
  ≅ affineChartWeilRestriction C (C tensor_A B)
        (ringBaseChange B (C tensor_A B) Y).
```

The theorem `affineChartWeilRestrictionTensorBaseChangeIso_comparison`
fixes this isomorphism by the exact all-test identity

```text
originalComparisonForG'(p >> baseChangeIso.hom)
  = affineChartWeilRestrictionTensorBaseChangeComparison(p).
```

Its proof rewrites composition with the canonical morphism as `eta_T(p)`
and applies the second representing equivalence's inverse law. In
particular, the output is an actual scheme isomorphism whose map agrees
with the transported original counit on every test.

## Actual projective-immersion specialization

The definitions
`projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv` and
`projectiveImmersionWeilRestrictionTensorBaseChangeIso` take an actual
immersion `i : Y.left -> ProjectiveSpace B n` with
`i >> projectiveSpaceToSpec B n = Y.hom`. They retain local finite type
and finite projectivity of `B/A`, and require neither an independent
separatedness premise nor `hY`.

The existing proofs `isSeparated_of_projectiveImmersion` and
`hasFiniteAffineNeighborhoods_of_projectiveImmersion` derive those two
premises from this geometry. The latter uses the actual ample projective
line bundle and affine neighborhoods of finite point sets. Base change
then supplies the needed geometry of `YR`, without a new projective
immersion as input. The specialized `_apply`, `_natural`,
`_symm_natural`, and `_Iso_comparison` theorems retain the same canonical
maps and all-test identities.

This is the actual projective-immersion interface for the quasi-projective
targets used in Conrad's Example 4.2. Over a general ring, an arbitrary
immersion alone is not used to infer quasi-compactness or finite type.

## Retained obligations

This module proves the algebraic tensor-base-change comparison. It does
not prove geometric preservation properties of the representing scheme,
decomposition of actual completed tensor algebras over all upper places,
Weil restriction for a product algebra, or compatibility of the resulting
maps with independently defined point topologies. Integral arithmetic
models, function-field completion instances, product and adelic-limit
arguments, and the global adelic homeomorphism of Example 4.2 remain
obligations of the whole-paper task. No whole-paper completion is claimed.
