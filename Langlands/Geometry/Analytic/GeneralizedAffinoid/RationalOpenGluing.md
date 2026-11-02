# Actual algebra descent on arbitrary topological open covers

Author: Worker 36.

Let `K` be a complete ultrametric normed field and `A` an actual presented
positive-polyradius affinoid `K`-algebra. This module constructs
`openAlgebraSheaf K A` on the ordinary topological opens of the actual
space `BanachSpectrum A`. Its underlying presheaf is definitionally the
compatible-family presheaf `openAlgebraPresheaf K A` from
`RationalOpenSections`. Its sections are elements of actual rational
quotient algebras, compatible under the actual bounded restriction maps.

For `U : I → Opens (BanachSpectrum A)`, where `I : Type v` and the field
belongs to `Type u`, `OpenSections.LocalCompatible U s` says that two
members of the local family have the same component at every actual
rational chart whose entire locus lies in both opens. It does not compare
only values at spectral points. The field and cover-label universes are
independent.

For each rational chart contained in the union of the opens,
`openRefinement` restricts the open cover to the chart's locus and applies
`FiniteOpenRefinement.ofOpenCover`. The resulting finite family has actual
bounded arrows to the target chart, labels in `I`, full component loci
contained in their labelled opens, and coverage by relative interiors.
Only pointwise coverage and full-locus subordination are needed in the
descent proof.

The private `finite_gluing` adapter applies the proved
`finiteRationalGluing` theorem to a lifted `Fin n` index type and retains
the original charts, quotient elements and restriction maps. Its
uniqueness implies the private `finite_ext`: equality of two elements of
the target quotient can be checked after restricting to a finite covering
family. To apply uniqueness, the restrictions of one element form a
compatible family because the two composites from an actual intersection
are the same arrow over `A`.

`glueChart c s hs` descends the component of each local section at its
labelled refining chart. The actual intersection chart lies in both
labelled opens. Section compatibility with the intersection restrictions,
together with `hs`, gives the matching equations required by finite
rational gluing. `glueChart_refinement` records that the descended element
restricts to the specified component on every member of `c`.

The key equation `glueChart_local` applies to every actual arrow `e ⟶ d`
whose source locus lies in any original open `U i`: the restriction of
the descended element is exactly the component of `s i` at `e`.
To prove this equation, the implemented proof covers `e` by its actual
intersections with the members of `c`. These intersections cover because
the arrow sends the locus of `e` into the locus of `d`. The uniqueness
of arrows over `A`, `glueChart_refinement`, each local section's
compatibility, and `LocalCompatible` identify both sides on every
intersection. `finite_ext` then gives the equation in `e.algebra`.
Thus the equation holds independently of the choices of finite
refinement; no common choice of refinements is assumed.

`glue s hs` assigns this descended element to every actual rational chart
contained in the union. To check compatibility along an arrow, refine its
source. The local-test equation for the target and the defining equations
for the source identify the two elements on every refining chart.
Finite separation proves the required equality. This constructs an
element of the original compatible-family section algebra on the union.

`restriction_glue` evaluates the local-test equation at the identity arrow
of each contained chart, proving that `glue` restricts to each original
section. `existsUnique` proves uniqueness by refining each rational chart
in the union and using the prescribed restrictions of any proposed
gluing, followed by `finite_ext`. No nonempty-cover or inhabited-label
assumption is used; the finite gluing theorem also handles empty families.

`localCompatible_iff_isCompatible` identifies the condition above with
Mathlib's usual presheaf compatibility on pairwise intersections of
opens. In one direction, a chart in an intersection is a common rational
test. In the other, evaluate the equality of the two restricted sections
at such a chart. This comparison itself needs no completeness hypothesis.

`openAlgebraPresheaf_isSheaf` applies
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing` to `existsUnique` through
this comparison. The required preservation of limits by the forgetful
functor is obtained from the equivalence of `CommAlgCat K` with the
undercategory of `K` in `CommRingCat`, followed by the two forgetful
functors. `openAlgebraSheaf` pairs the original presheaf with this proved
sheaf property. No sheafification changes its section algebras or maps.

The provenance is internal. The construction combines the concrete
sections and restrictions of `RationalOpenSections`, the constructed
relative finite rational refinements of `RationalChartOpenRefinement`,
the actual intersection maps, the proved finite rational quotient
descent theorem from `FiniteRationalGluingProof`, and pinned Mathlib's
ordinary topological sheaf criterion. The proof route is the finite
rational descent argument described above. No new original-literature
claim, private peer construction, or assumed sheaf is used.

Arbitrary positive real radii, trivial valuations, nilpotents, zero
algebras, and empty spectra and covers remain allowed. This construction
establishes the actual algebra sheaf on ordinary topological opens.
It does not construct local rings or stalk comparisons, identify it with
a separately stored sheaf on a general affinoid domain, or provide
unrestricted analytic atlases, etale sites or equivariant sites. Those
remain subsequent construction obligations.
