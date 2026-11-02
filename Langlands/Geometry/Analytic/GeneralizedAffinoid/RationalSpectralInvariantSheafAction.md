# Actions on the actual algebra sheaf and its whole-chart sections

Let `K : Type u` be a complete ultrametric normed field, `A` an actual
positive-polyradius presented affinoid algebra over `K`, and `G : Type v` a
topological group. Let `ρ : DomainSpectralAction G A` be a continuous action
for the represented-domain spectral topology, and let `H` be an open subgroup
of `G`. The field and group universes are independent.

All sheaves below are on the already constructed
`SpectralInvariantChart.finiteRationalTopology ρ H`. Objects are the actual
weighted rational quotient charts whose loci are preserved by every element
of `H`. Arrows are the original bounded restrictions. The topology uses finite
families covering the original loci and permits empty covering families for
empty loci. `SpectralInvariantChart.whole ρ H` is the published terminal whole
chart.

## Action on the ordinary algebra sheaf

`spectralInvariantSheafOperator ρ H g` is an endomorphism of the actual ordinary
algebra sheaf restricted from `algebraSheaf K A` along the continuous invariant
chart inclusion. At a chart `d`, its algebra homomorphism is exactly the one
underlying the bounded operator
`(spectralInvariantSectionAction ρ H d).obj.ρ g`. Published equivariance of
bounded restrictions proves naturality.

`spectralInvariantSheafAction ρ H` bundles these operators as an action of `H`
on that sheaf object. Identity and multiplication follow by evaluating the
existing bounded action laws on every section, then using extensionality of
algebra homomorphisms, natural transformations and sheaf morphisms. Its entire
underlying presheaf is the original algebra presheaf precomposed with the
invariant inclusion, as stated by `spectralInvariantSheafAction_presheaf`.
`spectralInvariantSheafAction_apply` identifies every operator on every
section.

`spectralInvariantSheafAutomorphisms ρ H` uses Mathlib's `Action.ρAut` to give
the resulting monoid homomorphism from `H` to automorphisms of the sheaf.
The equations ending in `_hom_apply` and `_inv_apply` identify its forward
operator with the original bounded operator at `g`, and its inverse with
the operator at `g⁻¹`. Thus the inverse sheaf maps are constructed as well.

## Evaluation, whole sections and structural maps

`spectralInvariantSheafSectionAction ρ H d` applies Mathlib's `sheafSections`
evaluation functor, lifted with `Functor.mapAction`, to the sheaf action.
Its algebra is exactly `CommAlgCat.of K d.obj.algebra`, and its operators are
the original bounded section operators with their bounds forgotten.
`spectralInvariantSheafSectionRestriction ρ H f` is the actual sheaf restriction
between these evaluated actions. Naturality of the sheaf operators proves
its equivariance; `_apply` identifies its algebra map with
`f.hom.restriction`.

`spectralInvariantBaseAlgebraAction ρ H` retains the ambient algebra `A` and
the operators `(ρ.toMonoidHom (g : G)).hom.toAlgHom`, using the already
constructed bounded ambient action restricted to `H`.

`spectralInvariantWholeSectionIso ρ H` is an isomorphism in
`Action (CommAlgCat K) H` from this ambient action to the sheaf action
evaluated on the actual terminal whole chart. Its underlying algebra
isomorphism is precisely the published `wholeSectionIso K A`, constructed
from the bounded whole-chart equivalence. The forward map is the whole
chart's original `baseMap`; the inverse is `wholeRetraction K A`.
The published section-action structural-map formula proves that this
particular isomorphism intertwines the two actions.

`spectralInvariantSheafBaseMap ρ H d` composes the whole-section
identification with restriction along `SpectralInvariantChart.toWhole ρ H d`.
It is therefore an equivariant algebra homomorphism from the original ambient
action to the evaluated section action. Its `_apply` and `_hom` equations
identify it with the original bounded structural map `d.obj.baseMap`, after
forgetting the bound. `spectralInvariantSheafBaseMap_naturality` proves that
these structural maps commute with every original invariant-chart restriction
as morphisms of actions.

## Provenance and scope

This is an internal construction from the published
`RationalSpectralInvariantActions`, `RationalSpectralInvariantSite`,
`RationalSpectralInvariantRestrictionSite`, and `RationalChartAlgebraSheaf`,
using Mathlib's sheaf evaluation and action constructions. The actual algebra
sheaf has an unconditional published sheaf proof. Its restriction uses a
proved continuous site inclusion. The bounded actions, restriction
equivariance, terminal whole chart and bounded whole-chart identification
are published constructed inputs. No new assertion is attributed to original
literature, and no descent, comparison isomorphism or sheaf action is assumed
as an output premise.

All positive polyradii and the supported trivial valuations, nilpotents,
zero algebras, empty spectra and empty finite covers are retained. The result
gives algebraic actions on a sheaf and its section algebras, with the specified
bounded antecedents. It asserts no continuity of algebra sections for a norm
or discrete topology. It stays on the finite invariant rational site of one
presented affinoid. Full invariant-domain sites, unrestricted analytic atlases,
analytic etale and quasi-etale sites, Berkovich's full equivariant etale site,
locally constant sheaf constructions, and the Harris tower remain separate
obligations.
