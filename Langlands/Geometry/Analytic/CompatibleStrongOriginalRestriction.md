# Restriction from the actual enlargement to original compatible maps

This is an internal consequence of the constructed full-domain enlargement,
coefficient coherence for a saturated source, and unique compatible extension.
It uses the explicit original local compatibility convention of
`CompatibleStrongMaps`. The input is any actual `StrongHom` between the
constructed enlarged presentations. There is no assumption that it was
obtained by extending an original map.

`BoundedAlgHom.transport` transports a complete bounded algebra homomorphism
along equalities of its presented source and target algebras. `transport_heq`
records the complete heterogeneous equality. `comp_heq` combines such
equalities for composition by eliminating the three proved algebra
equalities and then the two map equalities. The private chart-commutation
transport lemma performs the same elimination for chart functions and their
bounded spectrum pullbacks.

`saturatedAtlas_original_chart_heq` identifies an enlarged original chart
with its actual original chart function. The representative of that member
is the proved original whole-domain presentation; its ambient map is the
original chart. `saturatedAtlas_original_restriction_heq` identifies each
enlarged restriction between original charts with the actual original
bounded restriction. Its proof transports the local-domain arrow through
the two representative equalities and applies
`originalLocalDomain_restriction`. Thus both lemmas retain all the algebra
information in the chosen presentations.

For an enlarged map `F`, `original_admissible` transfers original
admissibility using the proved equalities of chart ranges.
`original_target_exists` first chooses an enlarged target containing the
image of an original source chart. That target lies in its original parent,
which supplies the required original containing target. No directedness or
greatest-chart hypothesis is needed.

`originalPullback F i j h` is the actual `F.pullback` at the two original
enlarged indices, transported along the two proved original algebra
equalities. Its heterogeneous recovery lemma is `originalPullback_heq`.
`originalPullback_chart` transfers the enlarged chart equation using the
complete chart and bounded-map equalities.
`originalPullback_naturality` transfers the entire two-variable enlarged
restriction equation, composing the original restriction identifications
and pullback identifications as full bounded maps.

`originalPullback_isMapChartChange` proves coherence of the restricted
family on every presented-affinoid coefficient test and every common
original target subchart. It transports the coefficient maps to the actual
enlarged original algebras, transfers the antecedent bounded factorization,
and applies the enlarged source's proved coefficient coherence. Transport
of the resulting complete bounded equation gives the original test equation.
The equivalence between coefficient coherence and the explicit local-domain
law then gives the compatibility field of `originalRestriction`. This
constructs an actual `CompatibleStrongHom A B`, with literal base map
`F.baseMap` and all original admissible bounded maps.

`originalRestriction_recovers` states full original bounded recovery as
`IsSaturationExtension`. Unique compatible extension consequently proves
`saturationExtension_originalRestriction`: extension of the restriction is
the entire original enlarged map, including every new source and target
pullback. In the other direction,
`originalPullback_saturationExtension` recovers every original admissible
bounded map in its literal original algebra types. Original coherent
extensionality yields `originalRestriction_saturationExtension`, equality
of the entire original compatible records.

`CompatibleStrongHom.saturationExtensionEquiv` packages actual extension
and restriction as inverse maps on the complete Hom sets. It includes both
the continuous maps and the full bounded pullback families. The resulting
`Full` instance for `CompatibleAtlasPresentation.saturationFunctor`,
together with its existing `Faithful` instance, makes that actual functor
fully faithful. Its already proved literal comparison with the ambient
space functor is preserved. No equality of bounded maps is inferred only
from their spectrum actions.

The base is a complete ultrametric normed field, without a nontrivial
valuation assumption. Original presentations have universes `u`, `v`, `w`;
the actual enlargements have chart indices in `v`. These results concern
the constructed enlargements of the two specified original presentations.
They do not assert essential surjectivity across arbitrary index universes.
Categorical equivalences, analytic localization comparisons, etale sites
and equivariant constructions remain subsequent work.
