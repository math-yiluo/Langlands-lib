# Actual complexes of equivariant sections

Author: Worker 13.

This module applies the constructed global, compact and smooth compact-section
functors to genuine complexes of equivariant ordinary-topological module
sheaves. It proves additivity of all three section functors by their underlying
linear maps. Mathlib's `Functor.mapHomologicalComplex` then constructs their
terms and differentials and proves that consecutive differentials compose to
zero. Its chain maps are obtained by applying the same functor to each
component.

`globalComplex`, `compactComplex` and `smoothCompactComplex` take values in
complexes of Mathlib representations. Every term of the last complex has the
proved smoothness property `smooth_term`. The category of algebraic
representations is abelian in Mathlib, so `globalHomology`, `compactHomology`
and `homologyOfSmoothComplex` construct actual homology representations and
intertwining maps. `smooth_homology` proves that the last representation is
smooth. First, injectivity of the actual cycle inclusion transfers each
open fixing subgroup from a term to its cycle. Then surjectivity of the
actual homology projection and equivariance transfer such a subgroup from
a representing cycle to its homology class. These use Mathlib's monomorphism
and epimorphism characterizations in `Rep`, without assuming a smooth
cohomology output.

`smoothCategoryComplex` constructs the same complex inside the published
category `Langlands.SmoothRep R G`. The natural isomorphism
`smoothCategoryComplexToRepIso` identifies its image in complexes of algebraic
representations with `smoothCompactComplex`. `smoothCategoryHomology` bundles
the actual algebraic homology using `smooth_homology`; its comparison
`smoothCategoryHomologyToRepIso` forgets only the smoothness witness.
This does not assume an abelian structure on the smooth category or assert
that its intrinsic homology functor has already been constructed.

The inclusions of smooth compact sections into compact sections and of compact
sections into global sections give actual natural chain maps.
`forgetSmoothHomology` and `forgetSupportHomology` apply the homology functor
to those maps. No arbitrary cohomology groups or comparison maps are supplied
as record fields.

`diagramFunctor` applies smooth compact sections to a genuine diagram of
sheaf complexes. `inverseSystemFunctor` specializes the index category to
the opposite of the ordered natural numbers, retaining all transition maps.
It does not take a derived inverse limit or assert that homology commutes
with that limit.
`smoothCategoryInverseSystemFunctor` retains the same complexes and transition
maps as objects of the published smooth category.

The complex shape and its indexing type are arbitrary; cochain complexes
over the natural numbers or integers are obtained with `ComplexShape.up`.
The ring, space and module universe is `u`, the group universe is `uG`, and
the complex and diagram indices have independent universes. All complexes
use the actual equivariant sheaf category from the companion modules.

## Provenance and remaining obligations

These are internal functorial constructions on the section functors, following
Mathlib's homological algebra. Berkovich, *Etale equivariant sheaves on p-adic
analytic spaces*, unfinished 1995–1996 manuscript, section 1.5, printed
pp.10–12, motivates resolutions and compact section cohomology; its
compact invariant-section construction appears on p.11. Worker 13 read the
original passages. The present constructions are ordinary-topological
infrastructure and make no comparison with the analytic etale site.

In particular, the input is a genuine complex, not an assumed cohomology
output. A supplied complex is not asserted to be an acyclic resolution.
Identification with derived equivariant cohomology requires a suitable
resolution and comparison theorem. This module does not construct Harris's
Ext spectral sequence or infer it merely from the existence of these
complexes. Smooth representation-category Ext, the analytic site, genuine
Shimura and local tower coefficients, and Galois continuity remain distinct
obligations with their existing owners.

Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The imported moving-space equivariant sheaf category, ordinary compact sections,
and general smooth representation category are present in Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The companion
`Equivariant/CompactSupport` and `Equivariant/SmoothCompactSupport` modules
construct the section functors used here.
