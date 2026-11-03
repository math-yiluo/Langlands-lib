# Automorphic actions on fpqc quotient group schemes

This module constructs an automorphic action on a specified quotient group
scheme. The base is any scheme `S : Scheme.{u}`, at every universe `u`.
The input consists of actual group schemes `H`, `G`, `Q` over `S`, an action
`a : AutomorphicAction H G`, and a homomorphism `q : G ⟶ Q` whose underlying
scheme morphism is quasi-compact, flat and surjective. Its additional hypothesis
is

```lean
a.IsStable (SubgroupFunctor.range (kernelι q))
```

Thus the full scheme-theoretic kernel is stable on every scheme test. No
smoothness, centrality, affineness, reducedness, or field assumption is imposed.
The construction does not assume that quotient points lift on their original
test scheme.

The entry definition is
`Langlands.GroupScheme.AutomorphicAction.onQuotient`. It returns an actual
`AutomorphicAction H Q`, with a scheme morphism as its action and all three
automorphic action laws on every test. This is descent of the acted-on group;
the existing `ActionDescent` module instead descends the acting group.

## Derivation and provenance

This is an internal derived construction. It uses the existing definitions of
`AutomorphicAction`, `IsStable`, `IsEquivariant`, subgroup-functor range, and the
actual kernel. In particular, it reuses
`Langlands.GroupScheme.mem_range_kernelι_iff` from `CentralIsogeny.Basic`,
which identifies kernel-range membership with being killed by `q` on every
test. Its use here requires no central-isogeny hypothesis.

The descent inputs are the published helpers
`Dynamic.flagQuotient_effectiveEpi_whiskerLeft` from `Dynamic.FlagQuotientAction`
and `AutomorphicAction.hom_ext_of_local_quotient_lift` from `ActionDescent`.
The former supplies the effective epimorphism of the underlying product map
`H.X ◁ q.hom.hom`; the latter checks equality after pulling a quotient point
back along `q`. These helpers are imported, without reconstructing their fpqc
arguments. The action-law and uniqueness proofs adapt the local-lifting method
of `ActionDescent` to the opposite factor. Worker 362 authored this module and
its documentation; Worker 1313 contributed that action-descent proof method.
There is no new external structural theorem or literature assertion.

## Fiber compatibility

`act_comp_eq_of_comp_eq` proves that, for any test `T`, acting point `h`,
and points `g`, `g'` with equal quotient images,

```lean
a.act h g ≫ q.hom.hom = a.act h g' ≫ q.hom.hom
```

Indeed, `g / g'` is killed by `q`, so stability puts `a.act h (g / g')`
in the same kernel. The automorphism `a.pointAut T h` preserves division.
After composing with `q`, its quotient is one, which gives the claimed equality.

`action_comp_preserves_quotient_fibers` projects a pair of maps into
`H.X ⊗ G.X` to their two factors and applies this argument. It proves that
`a.hom ≫ q.hom.hom` coequalizes every relation of `H.X ◁ q.hom.hom`.
`action_comp_preserves_quotient_scheme_fibers` proves the analogous assertion
for arbitrary maps of the underlying schemes: the common quotient image
supplies a common map to `S`, placing both maps in the same over-category.

`isStable_kernel_of_equivariant` proves the converse necessary condition.
For any action `b : AutomorphicAction H Q` making `q` equivariant, the image
of an acted-on kernel point is `b.act h 1 = 1`. This lemma requires none of
the quasi-compactness, flatness or surjectivity assumptions.

## The descended morphism and its laws

`onQuotientSchemeHom` applies `EffectiveEpi.desc` to the action followed by `q`.
`fac_onQuotientSchemeHom` is its factorization equation. Canceling the product
epimorphism proves that the new map lies over `S`; this gives `onQuotientHom`
and the equation `fac_onQuotientHom`:

```lean
(H.X ◁ q.hom.hom) ≫ onQuotientHom a q hk = a.hom ≫ q.hom.hom
```

`lift_onQuotientHom` evaluates this equation at a pair of test points, and
`onQuotientHom_naturality` proves compatibility with arbitrary test morphisms.

For `onQuotient`, the identity and acting-group multiplication laws are
checked after pulling back a single quotient point along `q`. The law of
preserving multiplication in `Q` is checked after two successive pullbacks,
so that each of the two quotient points lifts. The factorization equation
then reduces each law to the corresponding law of `a` and the group-homomorphism
law of `q`. Epimorphic cancellation gives the laws on the original test.

## Equivariance, uniqueness and exact criterion

`onQuotient_act_lift` is the all-test formula

```lean
(onQuotient a q hk).act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom
```

`onQuotient_isEquivariant` packages this as the existing predicate
`a.IsEquivariant (onQuotient a q hk) q`.

`onQuotient_hom_unique` applies equivariance at the universal pair of points
and cancels the effective epimorphism `H.X ◁ q.hom.hom` to identify action
morphisms. `onQuotient_unique` uses `ext_hom` to identify the bundled actions.
Finally, `exists_onQuotient_iff` states that an equivariant action on this
given fpqc quotient exists if and only if its actual kernel is stable.

This unit supplies action data once the group scheme `Q`, homomorphism `q`,
and its morphism properties are given. It proves no quotient existence,
quotient smoothness, relative dimension, or central subgroup existence. It
therefore leaves the corresponding geometric parts of
`CentralSmoothQuotientStatement` and the full `SemigroupOrderedProductStatement`
as separate obligations.
