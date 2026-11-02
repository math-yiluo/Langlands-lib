# Spectrum points and stalks on the finite rational chart site

Author: Worker 13. This is an internal construction from the published
positive-radius rational chart category, its actual intersections and
whole chart, and its finite-covering topology, using Mathlib's
`GrothendieckTopology.Point` and filtered-colimit construction. No new
literature theorem is assumed or attributed to this unit.

Fix an ultrametric normed field `K : Type u`, a presented affinoid algebra
`A` over `K`, and an actual multiplicative-seminorm point
`x : BanachSpectrum A`. The chart category retains its chosen finite
rational data, arbitrary positive real radii, unit-generation proofs,
actual closed quotient algebras and actual bounded restrictions over `A`.

`pointFiber x` sends a chart `d` to `ULift (PLift (x ∈ d.locus))`
in `Type u`. Its maps use the locus inclusion proved from the bounded
restriction. Each fiber is a subsingleton. `spectrumFiberEquiv` identifies
this type with the actual fiber
`{y : BanachSpectrum d.algebra // d.spectrumMap y = x}`. It uses the
existing spectrum/locus homeomorphism in both directions; the inverse
identities use that homeomorphism and proof irrelevance.
`spectrumFiberEquiv_naturality` shows that the comparison respects the
original bounded spectrum maps. These constructions do not require
completeness of `K`.

`PointNeighborhood x` is the category of elements of this fiber functor.
Its objects are actual charts containing `x`; its arrows retain the
original bounded restrictions and their equations on fibers.
Uniqueness of bounded restrictions gives subsingleton hom types.

From this point onward `K` is complete. The whole chart supplies a
neighborhood of every `x`. The constructed rational intersection of two
neighborhoods contains `x`, and its original projections give a common
refinement. Subsingleton hom types equalize parallel arrows. These
constructions prove that `PointNeighborhood x` is cofiltered.
The category is small in `u`, so Mathlib's essentially-small construction
supplies the initially-small condition.

`spectrumPoint x` is consequently an actual point of
`finiteRationalTopology K A`. For a covering sieve and an element of the
target fiber, the finite family in the covering witness contains a chart
through `x`. Its original arrow belongs to the sieve and sends the
source membership proof to the target proof. This proves the required
cover-lifting condition; it is not supplied as an input.

Let `E : Type uE` be a category with hom universe `vE` and colimits of
size `(u,u)`. The coefficient object and hom universes remain independent
of `u`, subject to this explicit colimit hypothesis. `presheafStalk E x`
is Mathlib's actual colimit functor over the opposite of
`PointNeighborhood x`. `stalk E x` restricts this functor to the actual
`E`-valued sheaves on the finite rational site.

`germ x d hx F` is the colimit injection from the sections of `F` on a
chart containing `x`. `germ_restriction` identifies the germ of a
restricted section with its original germ. `germ_naturality` proves the
compatibility with presheaf morphisms. `presheafStalk_hom_ext` states
that these chart germ maps jointly determine every map out of the stalk.
`presheafStalkDesc` constructs such a map from a family compatible with
all actual bounded restrictions; `germ_presheafStalkDesc` computes it on
each chart. `stalkCocone` displays this cocone on the original
neighborhood category, and `stalkCoconeIsColimit` proves its colimit
universal property.

If `E` also has finite limits and satisfies `AB5OfSize.{u,u}`, both stalk
functors preserve finite limits by exactness of these filtered colimits.
For a concrete coefficient category whose forgetful functor preserves
filtered colimits of size `(u,u)`, `germ_jointly_surjective` gives a
section representative for every stalk element. `germ_eq_iff` proves
that two sections on one chart have equal germs exactly when they agree
after an actual bounded restriction from a chart still containing `x`.
The latter statements use Mathlib's concrete filtered-colimit formulas.

This constructs points and stalks on the restricted finite rational
site over one fixed presented affinoid. It retains trivial valuations,
nilpotents, zero quotients and empty loci from the existing chart
framework. It does not assert that these spectrum points form a
conservative family: an arbitrary family of closed rational loci
covering all points does not by itself provide the finite family
required by the site's covering predicate. No enough-points theorem,
monic Godement unit, exact Godement resolution, full analytic or etale
site comparison, equivariant smoothness, support condition, Harris
tower or arithmetic specialization is asserted here.
