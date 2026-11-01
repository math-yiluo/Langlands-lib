# Norm-continuous sections of actual weighted rational domains

Authors: Worker 56 (weighted section-action and spectral-test adapters);
Worker 474 and Worker 36 (published strict fraction-continuity proof and route).
The required weighted stabilizer helper also adapts the proof by Worker 552.

This internal construction derives quotient-norm continuity of the actual
rational section action from norm-continuous base orbits and constructs
the corresponding positive spectral-test open subgroups in the original
group. The section operators are the previously constructed bounded
factorizations on the entire actual quotient algebra.

## Inputs and actual rational coordinates

The base field `K : Type u` is normed and ultrametric, and
`A : PresentedAffinoidAlgebra K` is an actual quotient of a finite
positive-polyradius Tate algebra by its chosen closed ideal.
A chart `d : RationalChart K A` retains denominator and numerator
representatives, arbitrary positive radii `s_j`, and the explicit proof
`d.generates` that their actual quotient classes generate the unit ideal.
Write these classes as `b = d.denominatorClass` and `f_j =
d.numeratorClass j`. Its structural map is the actual bounded
`i = d.baseMap : A → d.algebra`, and its rational quotient has
polyradius `A.polyradius.append d.radii`.

All declarations belong to
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.
The first three lemmas and the fraction abbreviation need no
`CompleteSpace K`.

`fractionCoordinate d j` is exactly the already constructed new rational
quotient coordinate.
`baseMap_denominator_mul_fractionCoordinate` exposes its actual equation
`i(b) * fractionCoordinate d j = i(f_j)`.
`isUnit_map_denominator` applies the published unit-denominator theorem,
using `d.generates`, then maps that unit through any actual bounded
`φ : d.algebra → B`.
`map_fractionCoordinate_eq_inverse_mul` maps the fraction equation and
cancels this unit, obtaining

\[
 \varphi(\operatorname{fractionCoordinate}_j)
   =\operatorname{Ring.inverse}(\varphi(i(b)))\,\varphi(i(f_j)).
\]

This is an algebraic identity on the quotient; no choice of spectral
point or faithfulness of spectrum evaluations is used.

## Continuity of all finite rational coordinates

From here assume `CompleteSpace K`. The actual presented targets are
then complete normed rings.
For a topological parameter space `T : Type v`, a center `x : T` and
actual bounded maps `φ(t) : d.algebra → B`, suppose every base-section
image `t ↦ φ(t)(i(a))` is continuous at `x`.

`continuousAt_map_fractionCoordinate` proves continuity at `x` on each
new fraction coordinate. The mapped denominator at the center is a
unit, so Mathlib's `NormedRing.inverse_continuousAt` applies there.
Compose it with the continuous denominator image and multiply by the
continuous numerator image. The preceding exact fraction identity gives
the desired coordinate continuity. This applies to a zero target too:
no target nontriviality hypothesis is added.

`continuousAt_map_coordinates` splits the actual quotient coordinate
index `Fin (A.arity + d.arity)` into its old and new blocks.
For an old coordinate, the published
`RationalPresentation.baseMap_coordinate` supplies the actual preimage
`coordinate K A i` in the base. For a new coordinate, the fraction
continuity lemma applies. Thus continuity on base sections implies
continuity on every coordinate of the actual weighted quotient.
Either block may be empty.

## The norm-continuous local section action

Let `G : Type v` be a topological group with its given topology and
`ρ : G →* Aut A`. Assume `hρ`: every forward base orbit
`g ↦ (ρ g).hom.toAlgHom a` is continuous in the actual quotient norm.
The weighted stabilizer construction derives the full open subgroup
`H_d = normOpenStabilizer ρ hρ d`, preserving the actual rational locus.
It constructs
`α_d = normSectionAction ρ hρ d : H_d →* Aut d.algebra`
by full represented-domain factorization.
Neither these section operators nor their continuity are new inputs.

`normContinuousSectionAction ρ hρ d` constructs an object of the
published `NormContinuousAction K H_d` category.
For a base section `i(a)`, the proved section base equation gives

\[
 \alpha_d(g)(i(a))=i(\rho(g)(a)).
\]

The right side is continuous in `g` by `hρ`, the subgroup inclusion and
bounded continuity of `i`. The preceding rational-coordinate theorem
gives every section-coordinate orbit's continuity at `1`.
The new generic `normContinuousActionOfCoordinates` constructor applies
to the actual quotient `d.algebra`. At the identity its coordinate
bounds are the original radius bounds, so that constructor derives a
common local contraction bound, extends continuity from finite monomial
sums to every quotient section, and translates identity continuity
along the group. No common bound on the section operators is assumed.

`normContinuousSectionAction_algebra` states that its algebra is exactly
`d.algebra`. `normContinuousSectionAction_actionAut` states that its
automorphism homomorphism is exactly `α_d`.
`continuous_normSectionAction` exposes continuity of every actual
section orbit in the original subspace topology on `H_d`.
This controls the whole quotient algebra, including nilpotents, and is
stronger than a statement only about evaluations at spectrum points.
No uniform contraction estimate for every element of `H_d` is asserted.

## Positive spectral-displacement tests in the original group

For `c : d.algebra` and `r > 0`,
`eventually_normSectionAction_sub_lt` makes
`‖α_d(g)(c)-c‖ < r` near `1` in `H_d`.
The displacement norm is continuous and has value zero at the identity,
so this follows directly from the preceding orbit theorem.

`normDomainSpectralSubgroup_mem_nhds` concerns the published subgroup
`DomainAutomorphism.domainSpectralSubgroup d.toDomain c r hr.le`
of the actual base automorphism group. Its conditions are preservation
of the represented rational locus and

\[
 \forall y\in\operatorname{BanachSpectrum}(d.\mathrm{algebra}),\qquad
   y(\alpha_d(g)(c)-c)\le r.
\]

Every normalized spectrum seminorm is bounded by the actual quotient
norm, so the norm-displacement neighborhood supplies this bound
simultaneously at all spectrum points. The inclusion of the derived
open subgroup `H_d` into `G` maps its identity neighborhood filter to
the ambient identity neighborhood filter. Consequently the preimage of
this entire domain test under `ρ` is a neighborhood of `1` in `G`.
Preservation of the locus is retained through membership in `H_d`.

`normSpectralOpenSubgroup` bundles that exact preimage as an
`OpenSubgroup G`, using `Subgroup.isOpen_of_mem_nhds`.
`mem_normSpectralOpenSubgroup` gives its exact criterion: a proof
`hg : g ∈ H_d` and the full spectral bound for the actual section
operator `α_d(⟨g,hg⟩)`. It uses all spectrum points and the displayed
section of the original quotient. The spectral bound uses `≤ r`;
strict positivity of `r` is required to derive openness.

For any finite index type `ι : Type t`, actual charts `d i`, actual
sections `c i`, positive tolerances `r i`, and a prescribed open
subgroup `U`, `finiteNormSpectralOpenSubgroup` is the intersection of
`U` and those full open test preimages.
Its membership theorem gives membership in `U` and all the original
locus and section conditions. Its containment theorem proves that the
constructed group lies in `U`. The charts need not form a cover, and
the sections need not be a matching family, for this finite simultaneous
test result.

## Provenance and scope

The fraction-inversion and finite-coordinate route adapts
`Langlands.Geometry.Analytic.StrictTestDomain.RationalSectionContinuityProof`,
whose proof is by Worker 474 and whose route was supplied by Worker 36.
The passage from section norm continuity to positive spectral tests
also follows the published strict `NormContinuousSpectralAction`
construction by Worker 36.
Worker 56 implements the actual arbitrary-radius rational adapters,
using the weighted `CoordinateContinuity` module and the represented-domain
section action. The included weighted stabilizer helper adapts the
strict proof by Worker 552, with Worker 36's route. All contributing
authors are credited in the submission.

The original geometric conventions are in Vladimir Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Example 1.2.2(v), printed/PDF p.4, gives arbitrary positive-radius
Tate algebras. Section 2.1's quotient-norm paragraph and Definition
2.1.2 on p.7 give the affinoid presentation setting; Definition 2.1.11
on p.8 uses bounded morphisms. Definition 2.2.1 and Exercise 2.2.2(ii)
on p.9 give full domains and the weighted rational quotient equations.
These pages were read directly.
The source's complete-field setting is retained for the local analytic
section construction. Its no-common-zero convention is represented here
by the Library chart's explicit unit-generation hypothesis; no
equivalence of those hypotheses is asserted.
The continuity criterion and positive-test conclusions above are
internal deductions from the published actual constructions, not
theorems quoted from those passages.

The field, group or parameter, and finite-index universes are independent.
The valuation may be trivial; radii are arbitrary positive real numbers,
without a value-group condition. Arbitrary chosen closed ideals,
nilpotents, zero algebras, zero arities, empty loci or spectra and empty
finite test families are allowed whenever the displayed data exist.
An empty simultaneous test family yields `U`.
No proper-ideal, reducedness, nonempty-locus or local-compactness
hypothesis is imposed.

Only specified actual rational domains receive these derived norm-continuous
section actions and spectral-test neighborhoods. This module makes no
claim about tests on arbitrary represented, compact or distinguished
domains, nor about equality of quotient and spectral norms.
It does not identify the full analytic automorphism topology, construct
general analytic or equivariant etale sites, prove quasi-etale lifting,
or construct the Harris tower.
