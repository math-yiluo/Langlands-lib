# Homomorphisms from a Weil restriction, restricted to the diagonal factor

Namespace `Langlands.GroupScheme.WeilAbelianImage`. This internal module is the second step of the
proof of `WeilAbelianImageTrivialityStatement`: it shows that a homomorphism `c` with commuting
values from the Weil restriction `H = R_{B/A}(G')` is trivial on the image of the embedding
`embNat` of `G'` (the "diagonal factor"). It uses the functors `resA`, `embNat` and the
equivalences `AffineWeil.pointsEquiv` of the Library module
`Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction`.

## Base change of test algebras

`A → B` is an algebra map, `T` an `A`-algebra and `M` a group scheme over `Spec A`.

- `tensorT B T` (abbreviation): `B ⊗[A] T` as a `B`-algebra.
- `inclT B T` (definition): the inclusion `T → B ⊗[A] T`, `t ↦ 1 ⊗ t`, as a map of `A`-algebras
  into the `A`-algebra underlying `tensorT B T`.
- `underA Y` (abbreviation): a `(B ⊗[A] T)`-algebra `Y`, regarded as a `T`-algebra through
  `inclT`. `underAMap` is the same construction on morphisms.
- `pointsEquivB M X` (definition): for a `B`-algebra `X`, the points of the base change `M_B`
  over `X` are the points of `M` over the underlying `A`-algebra (the Library equivalence
  `affinePointsBaseChangeMulEquiv`, inverted). `pointsEquivB_symm_naturality` is its naturality.

The test algebra, its inclusion and restriction of scalars reuse `WeilFactor.tensorB`,
`WeilFactor.incl` and `WeilFactor.liftU`. The point equivalence and its naturality use
`WeilChart.bPointsEquiv` and `WeilChart.bPointsEquiv_symm_naturality`.

## The restricted homomorphism

Assume `B` is finite, projective and étale over `A`, and `G'` is an affine group scheme of finite
type over `Spec B`. Let `c` be a homomorphism of group functors on `T`-algebras from `H` to `M`.

- `transferApp G' c Y` and `transfer G' c` (definitions): on a `(B ⊗[A] T)`-algebra `Y`, send a
  point `y` of `G'` over `Y` to `c (embNat y)` (a point of `M` over `Y` as a `T`-algebra), viewed as
  a point of `M_B` over `Y` through `pointsEquivB`. This is a homomorphism of group functors on
  `(B ⊗[A] T)`-algebras from `G'` to `M_B` (naturality of `embNat`, `c` and `pointsEquivB`).
- `app_embNat_eq_one`: if the values of `c` commute, `G'` is reductive and its geometric fibres are
  semisimple, then `c (embNat y) = 1` for every `(B ⊗[A] T)`-algebra `Y` and every point `y` of
  `G'` over `Y`. The values of `transfer G' c` commute (images of commuting values), so the base
  case `CommutatorTriviality.app_eq_one_of_semisimple` (module `AffineCommutatorTriviality`,
  applied over `Spec B`) shows `transfer G' c` is trivial, and `pointsEquivB` is injective.

## Provenance

Internal. In Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and its proof, the Weil
restriction becomes, after the base change `B ⊗_A -`, a product whose factors include `G'` itself;
this module handles that factor.
