# Radius-one comparison of norm-continuous affinoid actions

Author: Worker 56. The accompanying generalized action prerequisite was
developed by Worker 56 and Worker 36 from Worker 36's strict implementation.

This module extends the actual radius-one quotient comparison to the
categories of actions with continuous algebra-element orbits. Its inputs
are an ultrametric normed field `K : Type u` and a group `G : Type v`
with an arbitrary topology, in independent universes. Coefficient
completeness and continuity of the group operations are not required
for the algebra-category constructions. `IsTopologicalGroup G` is
required when bundling the jointly continuous spectrum actions.

For a strict quotient presentation `P`, write `E(P) = ofStrict K P` and
`e_P = strictEquiv K P : E(P) -> P`. The imported
`GeneralizedAffinoid/StrictComparison` construction uses the radius-one
coefficient-preserving isometry of restricted-series algebras, pulls back
the actual closed ideal, and constructs the induced quotient equivalence.
The equivalence preserves the quotient norm and is bounded in both
directions. Thus these are actual quotient algebras and actual bounded
maps; no new output algebra or comparison equivalence is assumed here.

For a strict action `X` on `P`, its image has algebra `E(P)` and action

```
rho_E(g)(a) = e_P^(-1)(rho_X(g)(e_P(a))).
```

`normContinuousAction_ofStrict` proves continuity of every such orbit:
the original orbit of `e_P(a)` is continuous by `X.property`, and
`e_P^(-1)` is continuous because it is a bounded algebra map.
`ofStrictActionFunctor` lifts the imported `ofStrictFunctor` on
Mathlib action categories to the full subcategories of continuous-orbit
objects. Its action and functor laws come from `Functor.mapAction` and
the full-subcategory lift. The object-algebra and action-evaluation
lemmas expose the displayed formulas.

For an equivariant bounded map `f : X -> Y`, the underlying image is
`ofStrictMap K f`, namely `e_Q^(-1)` after `f` after `e_P`.
`homMap_ofStrictActionFunctor_map` states this projection.
Conversely, `fromStrictActionMap` takes an equivariant map between image
objects back through the fully faithful action functor induced by
`ofStrictFullyFaithful`. Its underlying bounded map is
`fromStrictMap K h`, namely `e_Q` after `h` after `e_P^(-1)`, as stated
by `homMap_fromStrictActionMap`. Mathlib's fully faithful action
construction reflects equivariance, so the preimage is an actual arrow
of the strict continuous-orbit category.

`strictActionFullyFaithful` proves the two inverse equations on arrows.
The proofs apply the corresponding bounded-map inverse identities and
then the action-category hom-extensionality lemmas. The resulting `Full`
and `Faithful` instances say that every equivariant bounded map between
two image actions has a unique equivariant bounded preimage.
`strictActionForgetComparison` is the identity natural isomorphism
between forgetting the image action and first forgetting the strict
action and then applying `ofStrictFunctor`.

For a group `H : Type w` in a further independent universe and a
continuous homomorphism `f : H -> G`,
`strictActionRestrictionComparison` is the identity natural
isomorphism between restricting the strict action before embedding and
embedding before restricting the generalized action. Both paths retain
the same quotient algebra and bounded arrows, and their action at `h`
is conjugation of the original action at `f(h)`. The two functors are
definitionally equal. Neither restriction comparison requires
topological group operations.

On spectra, the imported actual homeomorphism
`strictSpectrumHomeomorph K P` sends `x` to the seminorm
`a -> x(e_P(a))`. Both action categories act on spectra by inverse
bounded pullback:

```
g • x = x after rho_X(g^(-1)).
```

`strictActionSpectrumHomeomorph_equivariant` proves that the
homeomorphism intertwines these actions, using the explicit
`BanachSpectrum.comap` on its generalized side. It applies
`strictSpectrumHomeomorph_naturality` to the actual bounded
endomorphism `rho_X(g^(-1))`. This is an equivariance result for the
concrete point actions and does not use continuity of group operations.

Under `IsTopologicalGroup G`, the imported strict and generalized
spectrum constructions already prove joint continuity from continuous
algebra-element orbits. `strictActionSpectrumIso` equips the same
homeomorphism with the proved equivariance equation, producing an
isomorphism in Mathlib's `ContAction TopCat G`. Its forward and inverse
evaluation lemmas give respectively
`x(e_P(a))` and `x(e_P^(-1)(a))`. The existing named
`NormContinuousAffinoidAction.topCatSelfForget` instance is installed
locally so that this category uses the actual underlying spectrum
topology through the identity functor on `TopCat`.

`ofStrictActionSpaceFunctor` is the opposite of the action-algebra
embedding. `strictActionSpectrumComparison` packages the preceding
isomorphisms as a natural isomorphism from the strict contravariant
spectrum functor to the generalized spectrum functor after this
embedding. Naturality follows from the imported pointwise spectrum
comparison for the underlying bounded map of every equivariant arrow.
The proof compares full-subcategory arrows, then action arrows, then
the continuous maps on points. No additional completeness assumption
is introduced: these action-spectrum functors use the direct
continuous-spectrum constructions.

The construction allows zero variables, unit ideals, zero quotients,
nilpotents, trivially valued fields and empty spectra. It assumes no
common operator-norm bound on the action. Full faithfulness does not
assert essential surjectivity onto arbitrary positive-polyradius
presentations. This module does not identify the norm-orbit condition
with the full analytic automorphism topology, compare arbitrary
affinoid presentations, or construct an atlas, analytic site or Harris
tower.

This is an internal derived comparison of the imported
`GeneralizedAffinoid/StrictComparisonFunctor`, strict
`NormContinuousAction`, and generalized `NormContinuousAction` APIs.
The quotient, spectrum and bounded-map context comes from Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009):
printed/PDF page 4, Example 1.2.2(v), Definitions 1.2.3 and 1.2.5 and
Exercise 1.2.4; page 7, Definition 2.1.2; and page 8,
Definition 2.1.11. The source's affinoid setting uses a complete
coefficient field. Here the incomplete-field scope is limited to the
already constructed normed quotients and their bounded spectra.
The equivariant motivation is Berkovich, *Etale equivariant sheaves on
p-adic analytic spaces* (unfinished manuscript, 1996), section 1.1,
printed/PDF pages 1–3. That source's continuous analytic actions use
the analytic automorphism topology and can change coefficient fields;
the fixed-field norm-orbit categories compared here are explicitly
internal prerequisites. Neither original states this particular
functor or natural isomorphism.

Registered originals: `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
and folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The original cited pages were read directly during this development.
