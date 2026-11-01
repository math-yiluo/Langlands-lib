# Renard II.2.1: stalk construction on a chosen basis

This module implements the neighborhood diagram and its lifted abelian-group
colimit from David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, printed p.34 / PDF p.40. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The precise passage runs from the ordered neighborhood set through the
canonical germ maps. The explicit representative description is a separate
obligation.
The supplementary 2010-edition errata, PDF pp.2–3, do not correct this stalk
passage.

`BasisNeighborhood B x` is the full subcategory of the opposite of the actual
basis-open category on objects containing the supplied point. Its arrows are
exactly reverse inclusions. Nonemptiness follows by refining the whole space
at that point. Filteredness follows by refining the intersection of two
neighborhoods and using thinness to equalize parallel arrows.

`neighborhoodDiagram` uses precisely the original section groups and restriction
maps. `stalkDiagram` then applies the standard additive-group universe lift.
For independent space universe `u` and group universe `v`, the lifted values
and the resulting stalk carrier lie in `Type (max u v)`. No comparison of `u`
and `v` is imposed. Mathlib's small colimit construction gives existence in
that joint universe; `rawStalkCocone` and `rawStalkIsColimit` exhibit the actual
colimit and its universal property.

`rawGerm` first inserts an original section into its lifted group, then applies
the colimit coprojection. It is an additive homomorphism. Its zero and addition
laws follow from that fact; restriction compatibility is the cocone law
evaluated on the lifted section. `rawStalkFunctor` takes colimits of the actual
diagram transformations; its identity, composition and evaluated germ laws
are inherited from colimit functoriality. `stalkFunctor`, `stalk`, `germ` and
`stalkMap` specialize to the existing normalized source category.
`stalkCocone` and `stalkIsColimit` expose the same universal property there,
and `germ_zero`, `germ_add`, `germ_restriction` and the `stalkMap` laws give
the corresponding normalized API explicitly.

The reverse-inclusion category and the universe lift realize the cited
directed-colimit construction. The intrinsic functoriality and germ laws are
derived categorical packaging: the diagram functor laws are checked
componentwise, and the stalk functor laws follow from the colimit functor.

No sheaf property, all-open extension, separation, compactness, global
nonemptiness, intersection closure, or nonzero group hypothesis is used.
Empty spaces are allowed, and an empty basis open cannot contain a supplied
point. The construction does not use representative-existence/equality results,
etale spaces, or sheafification.

Worker 1215 implemented the construction and intrinsic laws. Worker 633
contributed source and scope checks. Worker 6 supplied the original passage
audit and suggested the universe-lift and categorical construction route.
