# Local rings of the actual ordinary-open affinoid sheaf

Author: Worker 36.

Let `K` be a complete ultrametric normed field and let `A` be a
`PresentedAffinoidAlgebra K`. Rational charts retain their actual closed
positive-polyradius Tate quotient algebras and bounded restriction maps over
`A`. The ordinary-open sheaf and its stalks are the concrete compatible-family
constructions of `RationalOpenGluing` and `RationalOpenStalkResidue`.

This module proves that each genuine ordinary-open stalk `openStalk x` is a
nonzero local ring. Its maximal ideal is exactly the kernel of the constructed
evaluation `openStalkResidue x` in the actual completed residue field
`CompletedResidueField K x`. Locality and maximality are derived here.

## Restriction equations for actual representatives

For an actual rational arrow `f : e ⟶ d`,
`chartInteriorSection_restriction` identifies the restriction of the section
associated to `a : d.algebra` with the section associated to
`f.restriction a` on the interior of `e.locus`. The proof checks every
rational test chart in that interior. The two composites to `d` agree by
uniqueness of the actual bounded arrows over `A`.

`chartOpenGerm_restriction` then identifies their ordinary topological germs
at a point in both interiors. It applies the ordinary presheaf germ restriction
equation to these actual sections. The source and target opens are explicitly
the interiors of the respective closed loci.

`RelativeNeighborhood.mem_ambient_nhds` proves that a relative rational
neighborhood within `d.locus` is an ambient neighborhood when the chosen point
lies in the interior of `d.locus`. The subtype-neighborhood description supplies
an ambient neighborhood `V`; intersecting `V` with the neighborhood `d.locus`
gives a set contained in the refining chart. This topological observation does
not require completeness of `K`.

## An invertible representative on a smaller neighborhood

`exists_isUnit_restriction` starts with an actual element `a : d.algebra`
whose chart seminorm at an interior point `x` is nonzero. It constructs an
actual chart `e`, an actual arrow `f : e ⟶ d`, interior membership of `x`
in `e.locus`, and a proof that `f.restriction a` is a unit of `e.algebra`.

For the construction, the nonvanishing locus of the continuous function

```text
z ↦ d.locusHomeomorph.symm z a
```

is an open neighborhood of the point in the subtype `d.locus`.
`RelativeNeighborhood.ofNeighborhood` gives an actual rational refinement
whose entire locus lies in that nonvanishing locus. The ambient-neighborhood
lemma gives interior membership of `x`. For every spectrum point of `e.algebra`,
naturality of the actual spectrum/locus homeomorphisms identifies its value on
`f.restriction a` with the corresponding nonzero value in `d`.
The published `isUnit_iff_forall_spectrum_ne_zero` for arbitrary positive-radii
affinoid algebras then proves that the restriction is a unit.

The conclusion is invertibility in the actual quotient algebra. The proof uses
the spectrum criterion to establish this algebraic fact and retains all original
elements and restriction maps.

`UnitNeighborhood d x a` records the actual data: a refining chart, an actual
bounded arrow to `d`, interior membership of `x`, a unit in the refining quotient
algebra, and equality of its underlying element with the restriction of `a`.
`unitNeighborhood` constructs these data under the same nonvanishing hypothesis,
using `exists_isUnit_restriction` and choosing the unit supplied by its `IsUnit`
witness. Its output includes the unit and hence its inverse; it is a reusable
neighborhood construction for the specified original element.

## Locality and the maximal ideal

`openStalk_nontrivial` uses the already constructed unital map
`openStalkResidue x` into a field to prove that the stalk is nonzero.

`isUnit_iff_openStalkResidue_ne_zero` proves, for every element `t` of the
ordinary-open stalk,

```text
IsUnit t ↔ openStalkResidue x t ≠ 0.
```

A unit has nonzero image in the field. Conversely,
`exists_chartOpenGerm` represents `t` by an actual quotient element on a
rational neighborhood. The computed evaluation on that germ and
`norm_completedResidueEvaluation` imply nonvanishing of its chart seminorm.
The preceding smaller-neighborhood construction gives an invertible
restriction. Its image under the actual chart germ map is a unit, and
`chartOpenGerm_restriction` identifies that image with `t`.

`openStalk_isLocalRing` applies `IsLocalRing.of_nonunits_add`. A nonunit has
zero completed-residue evaluation by the established equivalence. The sum of
two such elements also evaluates to zero and hence cannot be a unit.
This proves the local-ring instance for the original ordinary-open stalk.

`openStalkResidueKernel_eq_maximalIdeal` identifies the existing evaluation
kernel ideal with `IsLocalRing.maximalIdeal (openStalk x)`: membership in each
is equivalent to being a nonunit. `openStalkResidueKernel_isMaximal` records
maximality of that same ideal. The earlier exact contraction theorem
`comap_openStalkResidueKernel` continues to identify its contraction along
`baseOpenGerm x` with the original seminorm kernel in `A`.

## Provenance and scope

This is an internal construction derived from the actual ordinary-open sheaf,
its completed-residue evaluation and rational neighborhood representative
theorem in `RationalOpenStalkResidue`, actual refinements in
`RationalChartOpenRefinement`, spectrum/locus naturality in
`RationalChartCategory`, and the published spectrum unit criterion in
`SpectrumIdealCriterionProof`. Pinned Mathlib supplies the topological germ
restriction equation, the subtype-neighborhood description and the algebraic
local-ring criterion and maximal-ideal description. Every new compatibility
and locality obligation is proved in this module. No new original-literature
assertion is claimed.

The hypotheses allow trivial valuations and arbitrary positive radii. There is
no reducedness or nonzero-algebra assumption on the base or chart algebras;
nilpotents are retained. Point-indexed conclusions are vacuous when the spectrum
is empty.

This module does not yet package a commutative-ring-valued locally ringed space,
identify the stalk residue field with the completed residue field, compare with
the stalk indexed by all closed rational charts containing the point, compare
with stored general-domain sheaves, construct arbitrary analytic atlases, or
construct analytic etale or equivariant sites. In particular, the evaluation
into the completed residue field is not asserted to be surjective.
