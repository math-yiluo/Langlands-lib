# Completed-residue evaluation of actual open sections and topological germs

Author: Worker 36.

Let `K : Type u` be an ultrametric normed field, `A` a presented
positive-polyradius affinoid algebra over `K`, and `x : BanachSpectrum A`.
The completed residue field is the existing actual normed field
`CompletedResidueField K x`, constructed from the quotient of `A` by the
seminorm kernel, its fraction field and completion. This module constructs
evaluation of rational quotient elements, compatible open sections and
ordinary topological germs in that field. It also proves that every
topological germ has a rational neighborhood representative.

For an actual rational chart `d` and `hx : x ∈ d.locus`,
`completedResidueEvaluation d x hx` is a bounded algebra homomorphism
from `d.algebra` to `CompletedResidueField K x`. It applies the existing
`RationalPresentation.liftFromBase` to `completedResidueMap K x` and the
actual fractions of the rational numerators by the denominator. The
previously proved bounds and equations on these fractions discharge the
extension's obligations. This uses the original closed Tate quotient
algebra, rather than replacing it by its spectral values.

`completedResidueEvaluation_comp_baseMap` and its elementwise version
identify the composite with the original completed-residue map from `A`.
For every actual bounded restriction arrow `f : d ⟶ e`,
`completedResidueEvaluation_restriction` proves that evaluation after
restriction equals evaluation on `e`. Its proof uses uniqueness of
bounded algebra maps from the rational quotient with a prescribed map
on `A`, the arrow's base-map equation, and the preceding composite
formula. This equation only requires membership in the full rational
loci, including their boundary points.

`norm_completedResidueEvaluation` identifies the norm of the evaluation
of each quotient element with the value of the unique spectral point
over `x`, given by `d.locusHomeomorph.symm ⟨x, hx⟩`. The proof compares
the pullback of the completed field's norm point with that point:
injectivity of the locus homeomorphism and the existing
`spectrumMap_pointLift` formula give equality. Applying both seminorms
to the element gives the asserted norm equality.

`OpenSections.pointChart U x hx` chooses an actual rational neighborhood
whose entire locus is contained in the ordinary open `U`. The neighborhood
and membership lemmas follow from `exists_rational_neighborhood`. This
choice and the chart evaluation constructions above do not require
completeness of `K`.

Assume henceforth that `K` is complete. `OpenSections.pointEvaluation`
evaluates an original compatible section family at the chosen rational
neighborhood and applies its bounded completed-residue evaluation.
`pointEvaluation_eq_chart` proves that every actual chart contained in
`U` and containing `x` gives the same result. The proof takes its actual
intersection with the chosen neighborhood, uses the section's two
restriction equations, and uses the evaluation restriction equations.
The alternative chart need not be a neighborhood of `x`.
`pointEvaluation_fromBase` recovers the original completed-residue map
on structural sections; this formula itself needs no completeness.
`pointEvaluation_restriction` proves compatibility under restriction
of ordinary opens by using the smaller open's chosen neighborhood
as a test chart in the larger open.

`algebraSheafedSpace K A` equips the actual spectrum with the constructed
`CommAlgCat K`-valued sheaf from `RationalOpenGluing`. Its presheaf is
definitionally `openAlgebraPresheaf K A`. `openStalk x` is Mathlib's
ordinary topological stalk of that presheaf, the colimit over the
opposite category of open neighborhoods of `x`. `openGerm U x hx` is
the original algebra-valued colimit injection.

For a chart `d`, `interiorOpen d` is the ordinary open interior of its
full locus. `chartInteriorSection d` sends a quotient element to its
compatible family on the full locus by `OpenSections.fromChart`, then
restricts that family to the interior. `chartOpenGerm d x hx` composes
this map with the topological germ map. Its hypothesis is
`x ∈ interior d.locus`, so it requires an actual neighborhood.

`exists_chartOpenGerm` proves that every element of `openStalk x`
is of this form. To apply Mathlib's concrete stalk representation
theorem, its proof obtains preservation of filtered colimits by
`forget (CommAlgCat K)` through `commAlgCatEquivUnder`, the forgetful
functor from the undercategory, and `forget CommRingCat`. Filtered
categories are connected, so the undercategory functor preserves
the required colimits. Mathlib then supplies a section representative
on an open neighborhood `U`. Choose `pointChart U x hx` and take the
section's actual component there. Compatibility of the family with
every bounded arrow into this chart identifies its restriction to
the chart's interior with `chartInteriorSection` of that component.
The original germ restriction equation proves equality of germs.

`openResidueCocone x` has the completed residue field as vertex and the
proved compatible `pointEvaluation` maps as legs on the actual open
neighborhood diagram. `openStalkResidue x` is the algebra morphism out
of the stalk obtained from its colimit universal property.
`openGerm_openStalkResidue` and `openStalkResidue_openGerm` compute it
on all section germs. `openStalkResidue_chartOpenGerm` computes it on
rational neighborhood representatives: it is exactly
`completedResidueEvaluation d x (interior_subset hx)`. The proof
uses the section-germ formula followed by naturality of chart
evaluation along the actual restriction from the chosen neighborhood.

`baseOpenGerm x` takes the global structural compatible family of an
element of `A` and then its topological germ. Evaluation of this germ
is `completedResidueMap K x`. Consequently it vanishes exactly on
`x.kernel`. `openStalkResidueKernel x` is the actual kernel ideal of
the stalk evaluation; it is prime because the target is a field.
`comap_openStalkResidueKernel` states the corresponding exact ideal
contraction along `baseOpenGerm`.

The provenance is internal. The module combines the published rational
quotient extension and its uniqueness, completed-residue construction,
actual chart intersections, rational neighborhood theorem, concrete
compatible section algebras and open sheaf, with pinned Mathlib's
ordinary stalk colimit and filtered-colimit representation theorem.
The proofs above describe the implemented route. No new
original-literature claim or private peer construction is used.

The hypotheses retain arbitrary positive radii, trivial valuations,
nilpotents and zero algebras. If the spectrum is empty, the assertions
indexed by a point are vacuous. This construction does not prove that
the topological stalk is a local ring or that its evaluation kernel
is maximal, or identify its algebraic residue field or completion
with the existing completed residue field. It does not equate this
topological stalk with `RationalChartPoint`'s stalk on all closed
rational charts containing `x`: a chart may contain `x` only on its
boundary. General-domain sheaf comparisons, arbitrary analytic
atlases, etale sites and equivariant sites remain subsequent work.
