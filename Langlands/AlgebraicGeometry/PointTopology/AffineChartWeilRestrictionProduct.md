# Actual finite-product decomposition of affine-chart Weil restriction

This module constructs the canonical finite-product decomposition of the actual
Weil schemes used in Conrad's Example 4.2. It compares separately constructed
schemes using an equivalence on every actual test scheme. The product
identification and its canonical maps are proved rather than supplied as
representability assumptions.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, Example 4.2, printed pp.9–10, specifically the second
Weil-restriction identity on p.10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad first base changes to the completed tensor algebra and then decomposes
restriction along its product of upper-place fields. The tensor base-change
step is treated in `AffineChartWeilRestrictionTensorBaseChange`. This module
treats the subsequent algebraic product step for finite projective algebras.
Its arbitrary-ring scope is a derived generalization of this source step.
The proof uses Mathlib's finite-product spectrum, universal coproducts and
pullback identities, and the existing affine-chart representing equivalence.

## Objects and hypotheses

All rings, schemes and the index type use a common arbitrary universe `u`.
Let `ι : Type u` be finite, let `A` be a commutative ring, and let `B i` be
commutative `A`-algebras, finite and projective as `A`-modules. No nonemptiness
assumption is made on `ι`; trivial rings are allowed. Write `P = ∀ i, B i` with
its ordinary product ring and product `A`-algebra structures.

Let `Y` be an actual scheme over `Spec P`, locally of finite type and separated,
and assume `HasFiniteAffineNeighborhoods Y.left`: every finite subset of its
actual scheme points lies in an affine open. Let `G` be the already constructed
`affineChartWeilRestriction A P Y`.

`finiteProductSpecProjection B i` is exactly the morphism
`π_i : Spec (B i) → Spec P` induced by `Pi.evalRingHom B i`.
`finiteProductFactorScheme B Y i` is the actual pullback `Y_i` of `Y` along
`π_i`, considered over `Spec (B i)`. Each `G_i` is the separately glued scheme
`affineChartWeilRestriction A (B i) Y_i`. Neither `Y_i` nor `G_i` is defined by
transporting the desired product identification.

The instance `finiteProductAlgebraProjective` derives projectivity of `P/A` by
identifying the finite dependent product with the dependent direct sum and
using projectivity of direct sums. Finiteness of `P/A` is Mathlib's finite
product module instance. Thus these properties of the product algebra are
conclusions from the factor data. Local finite type and separation of each
`Y_i` follow by base change. The finite-set affine-neighborhood property of
each `Y_i` follows from the proved `hasFiniteAffineNeighborhoods_of_affine`:
the projection `Y_i → Y` is affine, being the pullback of a morphism of affine
spectra. No geometry of a factor target is an additional assumption.

For the last two declarations the separatedness and finite-neighborhood
assumptions on `Y` are replaced by an actual relative immersion
`j : Y.left → ProjectiveSpace P n` with `j` followed by the projective-space
structure map equal to `Y.hom`. The existing projective-immersion adapters
derive the two premises. Local finite type and all algebra hypotheses remain.
This includes the source's quasi-projective input when given by such an
immersion. Over an arbitrary base, this formulation does not infer
quasi-compactness from the immersion alone.

## Actual factor coproduct and morphisms

`finiteProductPullbackCofanIsColimit B X` applies to every actual scheme `X`
over `Spec P`, with no finite-type, separation or neighborhood assumptions.
It states that `X.left` is the coproduct of the actual pullbacks `X_i`, with
their actual first pullback projections as injections. The proof starts from
Mathlib's finite-product spectrum isomorphism `sigmaSpec` and uses universality
of finite coproducts in schemes to pull this coproduct back along `X.hom`.
This works for arbitrary finite index types in the stated universe.

`finiteProductOverHomGlue B X Y` glues actual morphisms `X_i → Y_i` over
`Spec (B i)` using this source coproduct. The equation that the glued map lies
over `Spec P` is checked after every coproduct injection, using the relative
base equation of each given factor map and the pullback square. Its exact
restriction equation is `finiteProductOverHomGlue_fst`.

`finiteProductOverHomEquiv B X Y` gives

```
Hom_P(X,Y) ≃ ∀ i, Hom_(B i)(X_i,Y_i).
```

The forward map is precisely `(Over.pullback π_i).map`. The inverse is the
glued morphism. One inverse law uses source coproduct uniqueness; the other
uses the two pullback projections. `finiteProductOverHomEquiv_natural`
is functoriality under precomposition. The source coproduct is what makes
arbitrary independent factor morphisms sufficient.

## Test identification and all-test equivalences

`finiteProductSpecProjection_comp` proves
`π_i ≫ Spec.algebraMap A P = Spec.algebraMap A (B i)`.
For every actual test `T` over `Spec A`, `finiteProductBaseChangeTestIso B A T i`
identifies the pullback of `T_P` to `Spec (B i)` with the actual base change
`T_(B i)`. It is an isomorphism over `Spec (B i)`, constructed from Mathlib's
iterated-pullback isomorphism and the displayed structure-map identity. Its
forward and inverse naturality equations use actual pullback functor maps.
These test identifications and the factor affine-neighborhood lemma do not
require the index type to be finite.

`affineChartWeilRestrictionProductComparison B A Y T p i` is the canonical
map `T_(B i) → Y_i`: first precompose by the inverse of the test identification,
then use the factor pullback of the original comparison of `p : T → G`.
The original comparison is base change followed by the original glued counit.
This construction uses finite projectivity and local finite type; separation
and the neighborhood premise enter only for the equivalences below.
Its naturality theorem identifies comparison after precomposition by `f` with
precomposition by the actual `B i`-base change of `f`.

`affineChartWeilRestrictionProductTestEquiv` composes the original all-test
representing equivalence, the actual factor Hom equivalence and the test
identifications to obtain

```
Hom_A(T,G) ≃ ∀ i, Hom_(B i)(T_(B i),Y_i).
```

The apply theorem identifies each component with the separately defined
canonical comparison. Composing with the inverse of each independently proved
factor representing equivalence gives
`affineChartWeilRestrictionProductRepresentingEquiv`:

```
Hom_A(T,G) ≃ ∀ i, Hom_A(T,G_i).
```

Its naturality follows from naturality of the component comparisons and of
the existing factor inverses. Every statement here quantifies over arbitrary
actual test schemes, including nonaffine tests.

## Canonical product and counit formula

`affineChartWeilRestrictionProductProjection B A Y hY i` is obtained by
applying the representing equivalence to the identity of `G`.
`affineChartWeilRestrictionProductRepresentingEquiv_eq_comp` proves that
applying the equivalence to any `p : T → G` is exactly composition with this
fixed projection in component `i`.

`affineChartWeilRestrictionProductFan` equips `G` with these projections.
`affineChartWeilRestrictionProductFanIsLimit` proves its product universal
property. A cone is lifted by the inverse all-test equivalence. The forward
inverse law proves each projection equation, and injectivity proves uniqueness.
Consequently `affineChartWeilRestrictionProductIso` is the canonical isomorphism

```
G ≅ ∏ᶜ i, G_i
```

in the category of schemes over `Spec A`, obtained by uniqueness of limit
objects. The theorem `affineChartWeilRestrictionProductIso_hom_π` states that
its component projections are exactly the specified projections of `G`.

`affineChartWeilRestrictionProductProjection_comparison` and
`affineChartWeilRestrictionProductIso_comparison` fix the canonical map by an
exact identity for every test `T`, morphism `p : T → G` and index `i`: applying
the original counit comparison for `G_i` to `p` followed by the product
isomorphism and product projection equals the actual factor pullback of the
original counit comparison for `G`, precomposed by the inverse test
identification. The proof is the inverse law of the factor representing
equivalence, followed by the product projection identity.

`projectiveImmersionWeilRestrictionProductIso` and its comparison theorem
supply the same isomorphism and exact all-test identity from the actual
relative projective immersion, with separation derived internally.

## Retained obligations

This is the algebraic finite-product step of Example 4.2. It contains no
topological structure on any ring and no arithmetic realization of the index
type. The comparison of independently constructed local point topologies,
the actual completed tensor algebra and all upper-place factors, integral
models and the global adelic homeomorphism remain separate obligations.
In particular no assertion is made that `schemePointTopology` for values in a
nonlocal product ring coincides with a product of local point topologies.
Geometric preservation properties of the original Weil scheme and the other
sections of the paper are also not completed by this module.
