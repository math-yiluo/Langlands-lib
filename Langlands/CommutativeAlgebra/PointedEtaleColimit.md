# Strict locality of pointed étale colimits

This module isolates the ring argument used to construct a strictly local
affine limit of étale neighbourhoods. It abstracts the refinement step from
the pointed étale algebras in the Stacks Project’s construction of the strict
henselization. In the application the field of points is a separable closure
of the residue field of the base point. [The Stacks Project, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP),
[Lemma 10.155.11](https://stacks.math.columbia.edu/tag/04GW).

`Refines` says that an étale extension of a stage, equipped with a compatible
map to the field `Ω`, admits a map to a later stage over the original stage
and over `Ω`. The colimit inherits a map to `Ω`. An element whose image is
nonzero comes from a stage, and localization away from its representative
provides a pointed étale refinement in which the element is a unit. This
proves that the colimit is local and that the kernel of the map to `Ω` is its
maximal ideal.

To lift a simple root of a monic polynomial, filteredness puts its finitely
many coefficients in one stage and the monic polynomial lifting lemma gives a
monic lift there. Adjoining a root and inverting the derivative gives a
standard étale algebra with a point in `Ω`. Refinement sends its root to the
colimit and preserves the specified field value. Applying this to the residue
of an element of the colimit proves Hensel’s lemma.

If `Ω` is separably closed, the residue field embeds in `Ω` through the
local homomorphism to `Ω`. Each monic separable irreducible polynomial over
the residue field lifts to a monic polynomial over the colimit. A root of the
residue polynomial in `Ω` is simple, so the same refinement argument lifts it
to the colimit. Reducing gives a root in the residue field and proves that it
is separably closed.
