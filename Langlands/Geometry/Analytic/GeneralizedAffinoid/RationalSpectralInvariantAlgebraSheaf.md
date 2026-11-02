# Actual algebra sheaves with actions on the finite invariant rational site

Let `K : Type u` be a complete ultrametric normed field, `A` an actual
positive-polyradius presented affinoid algebra over `K`, and `G : Type v` a
topological group. Let `ρ : DomainSpectralAction G A` be continuous in the
constructed represented-domain spectral topology, and let `H` be an open
subgroup of `G`. The field and group universes are independent.

The site is the published `SpectralInvariantChart ρ H` with
`SpectralInvariantChart.finiteRationalTopology ρ H`. Its objects are actual
weighted rational quotient charts whose loci are preserved by every element
of `H`. Its arrows retain the original bounded restrictions. A covering sieve
contains a finite family of these charts covering the target's original locus;
the finite indexing type may be empty.

## The retained algebra sheaf

`spectralInvariantAlgebraSheaf ρ H` restricts the already proved
`algebraSheaf K A` along the continuous invariant-chart inclusion.
`spectralInvariantAlgebraSheaf_presheaf` identifies its entire presheaf with
the original algebra presheaf precomposed with that inclusion. This preserves
both the quotient algebras and all their algebra restrictions.

For an invariant chart `d`, `spectralInvariantAlgebraAction ρ H d` has underlying
object `CommAlgCat.of K d.obj.algebra`. Its operator at `g : H` is exactly the
algebra homomorphism underlying the published bounded
`spectralInvariantSectionAction ρ H d`. The identity and multiplication laws
follow by evaluating the corresponding bounded action laws on each section.
The equation `spectralInvariantAlgebraAction_apply` exposes this operator.

`spectralInvariantAlgebraPresheaf ρ H` assigns these actions to charts and the
original bounded restriction's algebra homomorphism to each opposite arrow.
The existing bounded restriction equivariance proves that these are morphisms
of actions. Their identity and composition laws retain the actual original
restrictions.

`spectralInvariantAlgebraPresheaf_forget` is an equality of complete functors:
forgetting the actions yields precisely the retained algebra sheaf's
presheaf, including its maps.

## Sheafness and formulas

`spectralInvariantAlgebraPresheaf_isSheaf` applies Mathlib's
`Presheaf.isSheaf_of_isSheaf_comp` to
`Action.forget (CommAlgCat K) H`. Mathlib's action forgetful functor reflects
limits of all required sizes. Its composite here is definitionally the
restricted, already proved algebra sheaf. Thus this is a proof of sheafness
of the constructed presheaf, with no extra descent or gluing premise and no
restriction identifying the group universe with the field universe.

`spectralInvariantEquivariantAlgebraSheaf ρ H` bundles this presheaf and proof
as a sheaf with values in `Action (CommAlgCat K) H`. The following equations
describe its actual values and maps:

- `spectralInvariantEquivariantAlgebraSheaf_forget` identifies the entire
  forgotten presheaf with `spectralInvariantAlgebraSheaf ρ H`.
- `spectralInvariantEquivariantAlgebraSheaf_obj` retains each original quotient
  algebra.
- `spectralInvariantEquivariantAlgebraSheaf_action_apply` retains each original
  bounded section operator after forgetting its bound.
- `spectralInvariantEquivariantAlgebraSheaf_map_apply` sends a section along
  `f : d ⟶ e` to `f.hom.restriction` of that section.
- `spectralInvariantEquivariantAlgebraSheaf_baseMap` states that the operator
  at `g : H` sends `d.obj.baseMap a` to
  `d.obj.baseMap ((ρ.toMonoidHom (g : G)).hom.toAlgHom a)`.
- `spectralInvariantEquivariantAlgebraSheaf_restrict_baseMap` states that
  restricting `e.obj.baseMap a` along `f : d ⟶ e` gives `d.obj.baseMap a`.

## Provenance and scope

This is an internal construction from published
`RationalSpectralInvariantActions`,
`RationalSpectralInvariantRestrictionSite`, and `RationalChartAlgebraSheaf`,
using Mathlib's `CategoryTheory.Action.Limits` and its sheaf reflection lemma.
The quotient algebras, bounded action operators, restriction equivariance,
finite invariant site, continuous inclusion and unconditional rational sheaf
proof are existing constructed inputs. No new assertion is attributed to an
original-literature source.

The construction retains arbitrary positive polyradii, trivial valuations,
nilpotents, zero algebras, empty spectra and the permitted empty finite covers.
The output records algebraic actions whose operators have the published bounded
antecedents. It does not assert continuity for a norm topology or a discrete
topology on algebra sections.

This is the finite invariant rational site over one actual presented affinoid.
It does not construct a finite site of all invariant full domains, an
unrestricted analytic atlas, an analytic etale or quasi-etale site, Berkovich's
full equivariant etale site, or the Harris tower. Those are remaining
construction obligations of the host task.
