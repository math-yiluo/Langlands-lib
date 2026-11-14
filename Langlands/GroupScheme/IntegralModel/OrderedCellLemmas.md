# Ordered products through represented subgroups and integral comparison lemmas

Module `Langlands.GroupScheme.IntegralModel.OrderedCellLemmas`. Internal derived
infrastructure for the integral open cell; all declarations are at an arbitrary
universe `u` and none is a separate literature statement.

## Ordered products inside a represented subgroup

Let `G` be a group scheme over any base scheme, `V` a subgroup functor represented
by `jU : U ⟶ G`, and `F r` subgroup functors represented by `j r : H r ⟶ G`, with
`range (j r) ≤ V` for every `r : Fin n`.

- `RelativeRoot.isIso_orderedMultiplication_factorHom_iff`: the internal ordered
  multiplication of the canonical factorizations `(∏ H r) ⟶ U` is an isomorphism
  exactly when, on every test scheme, every point of `V` is uniquely an ordered
  product (in the given order) of points of the `F r`. The proof uses the published
  bijectivity criterion `isIso_orderedMultiplication_iff_existsUnique`, the point
  equivalences of representing schemes and the monomorphy of `jU`.
- `RelativeRoot.isIso_orderedMultiplication_factorHom_of_isIso`: consequently this
  isomorphy does not depend on the chosen representatives of `V` and the `F r`.
- `RelativeRoot.isIso_orderedMultiplication_factorHom_of_iso`: an isomorphism
  `e : (∏ H r) ≅ U` with `e ≫ jU` equal to the ambient ordered multiplication
  makes the internal ordered multiplication an isomorphism (it equals `e` by
  monomorphy of `jU`).

## Cocharacter and root lemmas over a base

- `groupHom_neg_comp_eq_oppositeCocharacter_overBase`: over any base, negating a
  cocharacter of a commutative group scheme is precomposition with inversion of
  `Gm`, i.e. the published `Dynamic.oppositeCocharacter`. The proof is that of the
  published field version.
- `RelativeRoot.subgroup_le_dynamicUnipotent_of_isDomain`: over the spectrum of a
  domain, a positive lattice pairing places the actual root subgroup functor in the
  dynamic unipotent subgroup functor. The proof is that of the published field
  version, using the endomorphism lattice of `Gm` over a domain.

## Closed immersions with generic isomorphism

For a commutative ring `R` and a field `K` with `IsFractionRing R K` (no domain
hypothesis is used here):

- `flat_specAlgebraMap` and `isSchemeTheoreticallyDominant_specAlgebraMap`: the
  morphism `Spec K ⟶ Spec R` is flat and scheme-theoretically dominant.
- `isIso_of_isClosedImmersion_of_isIso_pullback`: a morphism `f : X ⟶ Y` over
  `Spec R` whose underlying scheme morphism is a closed immersion, with `Y` flat
  over `Spec R`, is an isomorphism when its pullback to `Spec K` is. The generic
  projection of `Y` is scheme-theoretically dominant (flat base change of a
  dominant morphism) and factors through `f`; hence the kernel of `f` is trivial
  and the closed immersion is an isomorphism (Mathlib
  `IsClosedImmersion.isIso_iff_ker_eq_bot`).
