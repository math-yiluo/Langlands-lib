# Reflection of Renard Noetherianity

Worker 1582. Internal derived infrastructure for the proof of Renard VI.7.5,
Proposition, printed page 186 / PDF page 192, in David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July
2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes
reductifs p-adiques (2026 version)--2026.pdf`.

The source applies a faithful exact functor `R` into a Noetherian category
and pulls back stabilization of ascending subobject chains. This module
isolates and proves that categorical transfer argument with independent
object and morphism universes for the two categories. The more general
monomorphism-preserving, isomorphism-reflecting version is derived here; it
is not presented as a separately stated result of Renard. The Noetherian
predicate is exactly the maximal-element definition of Appendix
A.I.3, printed page 248 / PDF page 254.

## Construction and implemented proof

For a functor `F` preserving monomorphisms, `functorSubobjectMap F X` sends
each actual subobject to the class of the image under `F` of its chosen
representative monomorphism. Mapping the factorization for an inclusion
proves monotonicity. This construction does not assume that `F` is full
or that every target subobject arises in this way.

If `F` also reflects isomorphisms, the map preserves strict inclusions.
For an inclusion `P < Q`, an isomorphism between the mapped inclusion's
source and target would reflect to an isomorphism between the original
representatives. Its commuting factorization would give `P = Q`, a
contradiction. Mathlib's strict-subobject criterion packages precisely
this implication.

`noetherianObject_of_functor` composes a hypothetical strictly increasing
sequence of source subobjects with this strict map, contradicting
Noetherianity of the image object. The published
`noetherianMathlibComparison` identifies the resulting Mathlib predicate
with Renard's maximal-element definition. Thus there is no extra chain
stabilization assumption.

`noetherianCategory_of_functor` additionally assumes source subobject
unions, preservation of finite-type objects and the actual target
Noetherian-category predicate. Applying the objectwise reflection to
each finite-type source object proves the category predicate.

For a faithful additive functor between abelian categories, faithfulness
reflects monomorphisms and epimorphisms, and balancedness reflects
isomorphisms. Renard's `SequenceLeftExact` supplies preservation of
monomorphisms. These facts give
`noetherianObject_of_faithful_leftExact` and
`noetherianCategory_of_faithful_leftExact`. Two-sided exactness can be
used through its left-exact conjunct; the implemented transfer does not
need its right-exact conjunct.

## Scope

The generic transfer theorem is proved. It neither constructs the
cuspidal Jacquet functor `R`, proves its faithfulness or finite-type
preservation, nor proves that its target is Noetherian. It does not
discharge either exact represented-group VI.7.5 target.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
