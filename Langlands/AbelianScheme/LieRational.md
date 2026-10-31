# The relative Lie functor on rational homomorphisms

This internal construction extends the published additive Lie functor to the
actual rational category of abelian schemes. It uses
[LieAction](LieAction.md), [Rational](Rational.md) and
[RationalizationLift](../CategoryTheory/RationalizationLift.md).
No further external theorem or existence hypothesis is introduced.

Let `S` be a scheme, `R` a commutative ring with a rational algebra structure,
and `p : S ⟶ Spec R` an actual scheme morphism. The rational scalar action on
module-sheaf morphisms is `rationalLinearOverBase p`: rational numbers map into
global functions through the structure morphism and then restrict to every
open. The construction requires this base data.

`rationalLieFunctor p` is the existing tensor extension of `lieFunctor S`.
Its objects are the actual relative Lie module sheaves; its morphism map
`lieMap0 p` sends `q ⊗ f` to `q • lieMap f`. The tensor universal property
supplies the linear map on Hom. The file proves the identity, composition and
addition formulas and bundles rational linearity as `lieMap0Linear`.
The integral inclusion recovers the original Lie functor through the
constructed natural isomorphism `rationalLieInclusionIso`.

On endomorphisms this map is definitionally the published `lieEnd0Action`.
Thus `lieRationalOrderAction p A α` composes an actual ring map
`α : O →+* End0 A` with that endomorphism action. For an integral action followed
by `endToEnd0`, the result equals the integral Lie action. Both endomorphism
rings use reverse categorical composition as multiplication, as in their
published definitions.

`lieIso0 p e` maps an actual isomorphism in the rational category to an actual
isomorphism of Lie sheaves. Its two maps are the constructed differentials of
`e.hom` and `e.inv`; the functor proves both inverse laws. It preserves identity,
inverse and composition. No arbitrary output isomorphism is supplied or
selected.

If `f` intertwines two rational order actions, applying the constructed
differential to that equality and using composition preservation proves
`lieMap0_intertwines`. This is a derived property of rational morphisms and the
Lie functor. No compatibility of the canonical Lie base-change comparison is
assumed or proved here. The file also makes no claim that an arbitrary isogeny
on an arbitrary base is invertible in the rational category; the isomorphism
`e` includes its actual rational inverse.
