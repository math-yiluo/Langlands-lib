# Renard II.2.1: normalized presheaves on an actual basis

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, printed p.33 / PDF p.39, from the opening basis
paragraph through equation (II.2.1.1). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read and visually checked. The separately registered
2010-edition errata, PDF pp.2–3, do not correct these definitions; their later
sheafification corrections are outside this unit.

`OpenBasis X` chooses a set of actual `TopologicalSpace.Opens X` and requires
Mathlib's `IsTopologicalBasis` for its image as subsets of `X`, using the supplied
topology. `OpenBasis.exists_subset` and `OpenBasis.isOpen_iff` expose precisely
the source's pointwise refinement property and its determination of openness.
No topology is replaced. The basis need not contain the empty open or any
intersection. No separation, local compactness or countability is assumed.

`BasisOpen B` is the full subcategory of actual open sets that belong to the
chosen basis. `basisInclusion` is its fully faithful inclusion into the open-set
category. `basis_hom_nonempty_iff`, `basisHom` and the subsingleton instance say
that its morphisms are exactly the unique inclusion arrows.

`RawPresheaf B` is the actual contravariant functor category from these basis
opens to `AddCommGrpCat`. The space universe `u` and group-carrier universe `v`
are independent. `Sections` evaluates that functor, and `restriction` is its
map on an opposite inclusion. The identity and composition theorems expose
Renard's restriction laws, including their elementwise forms. These proofs use
the functor laws; they do not assume any sheaf property.

A bare functor would omit the explicit source requirement that the value on
the empty basis open is the zero group. `IsNormalized` imposes subsingleton
values on every basis object whose underlying open is empty.
`isNormalized_iff_zero` proves this is equivalent to every element of each such
value being zero. The proof uses the existing group zero in one direction and
transitivity through zero in the other. When empty is absent the condition is
vacuous. `Presheaf B` is exactly the full subcategory satisfying this condition,
and `presheafInclusion` forgets it. Its morphisms are actual natural
transformations, exposed by `presheafHomEquiv`, with the componentwise identity
and composition laws. `restriction_naturality` and its evaluated version are
(II.2.1.1): the component after restriction equals restriction after the larger
component. `empty_section_eq_zero` exposes normalization on bundled objects.

The categorical implementation and the intrinsic construction laws are derived
formal packaging of the cited definitions. Worker 595 implemented them after
reading the original; Worker 6 contributed the source audit and the suggested
full-subcategory packaging. Stalks, basis extension and sheafification are not
used here.
