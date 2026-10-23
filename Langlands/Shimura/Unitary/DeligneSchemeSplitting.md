# Complex splitting of the Deligne group scheme

Author: Worker 57.

This module constructs an isomorphism of actual group schemes over `Spec ℂ`
between the pullback of the existing real Deligne group scheme and the product
of two copies of the existing multiplicative group scheme. Its point formulas
recover evaluation at the two complex roots of the quadratic relation.

## Internal provenance and scope

The construction is an internal consequence of four existing ingredients:
`DeligneGroupScheme` constructs the real group scheme from its explicit
coordinate algebra; `DeligneSplitting` splits the quadratic unit functor over
complex algebras; `CorepresentedPoints` recovers its points on arbitrary schemes
from relative global sections; and `GroupScheme.Multiplicative` provides the
actual multiplicative group scheme and group-valued Yoneda reconstruction.
No additional external theorem is asserted here. The original conventions of
the real source remain those documented in the imported Deligne modules.

The base rings are the concrete `ℝ` and `ℂ`, and schemes are in the corresponding
small universe. Test schemes may be nonaffine or nonreduced. There is no added
smoothness, finite-type, reducedness, field, nonemptiness or representability
hypothesis on a test scheme. The output group schemes and their isomorphism are
constructed; none is an input assumption. The contribution does not prove
smoothness or reductivity, a global arithmetic unitary-group splitting, or PEL
representability, canonical models, scheme levels or coefficient descent. Those
remain separate obligations of the host task.

## The actual source and target

`complexBaseMap` is `Spec.map` of the usual scalar inclusion `ℝ → ℂ`.
`complexGroupScheme` applies the actual pullback functor along this map to
`DeligneTorus.groupScheme`. Thus it is the complex base change of the previously
constructed real group object, with the group law transported by pullback.

`complexPointsEquiv T` first uses the pullback point equivalence to regard a
`T`-point as a point of the real group scheme on `T` regarded as a real scheme.
The relative Spec/global-sections adjunction then identifies this group with
`Points Γ(T.left, ⊤)`, the units of the quadratic algebra with relation
`ω² = -1`. The restriction identity `complexPointsEquiv_naturality` combines
naturality of these two equivalences. Its coefficient map is exactly the map
`a.left.appTop.hom` on global sections for an arrow `a : T' ⟶ T`.

The local `complexGlobalAlgebra T` is the complex-algebra structure on relative
global sections supplied by `algΓ (CommRingCat.of ℂ)`. In particular this scalar
action comes from the test scheme's structural morphism. Composing with the
existing quadratic splitting gives `complexSplitPointsEquiv T`, valued in two
copies of the global unit group. Its naturality follows by applying
`splitPointsEquiv_natural` to the complex-algebra homomorphism furnished by
`algΓ.map a`. The underlying ring map is the same global-sections map as above.

`splitGroupScheme` is the Cartesian monoidal product of two copies of
`GroupScheme.Gm (Spec ℂ)`, regarded as group objects. The helper
`productPointsEquiv` is a definitionally equal compatibility wrapper for
`Langlands.GroupScheme.productPointsEquiv` in `GroupScheme.Products`. It
works for arbitrary group schemes over any same-universe
base scheme: a point of their product corresponds to the pair of composites
with the projections. Multiplicativity follows because both projections are
monoid morphisms. `splitSchemePointsEquiv T` composes this product comparison
with the existing global-unit comparison for each copy of `Gm`. Its naturality
is proved componentwise by associativity of composition and naturality of the
`Gm` comparison.

## Isomorphism and formulas

`complexSplitting_naturality` identifies the two natural comparisons to pairs
of global units. Its proof applies the injective target comparison, then uses
the two restriction identities and cancellation of each equivalence with its
inverse.

`complexSplitting : complexGroupScheme ≅ splitGroupScheme` applies
`GroupScheme.isoOfPoints` to this natural family of multiplicative equivalences
on **all** test schemes. The existing group-valued Yoneda construction supplies
actual group-scheme morphisms in both directions and proves both composites are
identities. Restriction to affine points is not being used as a substitute for
that reconstruction.

`complexSplitting_hom_points` states that postcomposition with the forward
isomorphism gives `complexSplitPointsEquiv T` under the target point comparison.
`complexSplitting_inv_points` states the reverse identity for postcomposition
with the inverse isomorphism. Both proofs use the point formulas of
`isoOfPoints` followed by cancellation of the corresponding equivalences.

Writing `a + bω` for the quadratic unit corresponding to a point of the source,
and `i_T` for the image of `Complex.I` in its global sections,
`complexSplitting_hom_fst` and `complexSplitting_hom_snd` say that the two unit
values after the forward isomorphism are `a + b i_T` and `a - b i_T`, in that
order. `complexSplitting_hom_norm` identifies the existing quadratic norm of
the original unit with the product of these two unit coordinates. These follow
from `complexSplitting_hom_points` and the already proved algebraic splitting
formulas. The norm assertion is a formula on every test-scheme point; this
module does not introduce a separately named norm morphism of group schemes.
