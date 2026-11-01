# Weighted rational-locus stabilizers from norm-continuous algebra orbits

Authors: Worker 56 (weighted extension and represented-domain adapters);
Worker 552 and Worker 36 (the published strict rational perturbation argument
adapted here).

This internal construction extends the strict, unit-radius perturbation proof
to every actual `RationalChart K A` with arbitrary positive real radii.
Its hypotheses concern the quotient norm on the actual presented affinoid
algebra and the given topology on the parameter group.

## Data and conventions

The base field `K : Type u` is normed and ultrametric. The base algebra
`A : PresentedAffinoidAlgebra K` is the actual quotient of a finite
positive-polyradius Tate algebra by its chosen closed ideal. A chart
`d : RationalChart K A` retains its denominator and finite numerator tuple
as representatives in that Tate algebra, positive real radii `r_j`, and the
proof `d.generates` that their actual quotient classes generate the unit ideal.
The abbreviations `denominatorClass` and `numeratorClass` apply the actual
`presentationMap K A` to those representatives; write their values as `b`
and `f_j`. Every norm in this module is the quotient norm on `A`.

The locus is exactly

\[
  V=d.\mathrm{locus}
   =\{x\in\operatorname{BanachSpectrum}(A):
                       x(f_j)\le r_j x(b)\text{ for every }j\}.
\]

The existing action of `Aut A` on this spectrum is inverse pullback:
`(g • x)(a) = x(g.inv(a))`. Thus `locusStabilizer d` is the full subgroup
of bounded algebra automorphisms with image of `V` equal to `V`.
`mem_locusStabilizer` exposes this literal set equality. It requires
neither pointwise fixedness nor preservation of the displayed representatives.

Let `G : Type v` be a topological group, in a universe independent of `K`,
and let `ρ : G →* Aut A`. The hypothesis `hρ` says that for every actual
element `a : A`, the forward orbit
`g ↦ (ρ g).hom.toAlgHom a` is continuous for the norm topology on `A` and
the original topology on `G`. No topology on `Aut A`, uniform operator
bound, or domain-preservation hypothesis is supplied.

## Weighted perturbation proof

`exists_pos_le_denominator` proves the existence of a real `ε > 0` with
`ε ≤ x(b)` for every `x ∈ V`. The published
`RationalPresentation.isCompact_locus` gives compactness of the actual
closed inequality locus. The published `denominator_ne_zero`, using
`d.generates`, excludes `x(b) = 0` on that locus. Indeed, a zero
denominator would force all numerators to evaluate to zero, contradicting
unit generation. Nonnegativity of a spectrum seminorm therefore makes
the denominator evaluation strictly positive. The continuous evaluation
and Mathlib's `IsCompact.exists_forall_le'` give the positive uniform
lower bound, including the case of an empty compact locus.

`comap_mem_locus_of_displacement_lt` treats any actual bounded algebra
endomorphism `φ : BoundedAlgHom K A A`. Given a denominator bound `ε`,
it assumes

\[
  \|\varphi(b)-b\|<\varepsilon,\qquad
  \|\varphi(f_j)-f_j\|<r_j\varepsilon\quad\text{for every }j.
\]

For `x ∈ V`, the spectrum bound by the norm gives
`x(φ(b)-b) < ε ≤ x(b)`. The imported nonarchimedean seminorm theorem and
`IsNonarchimedean.add_eq_right_of_lt` imply `x(φ(b)) = x(b)`.
For each numerator the same strong triangle inequality gives

\[
 \begin{aligned}
 x(\varphi(f_j))
 &\le \max\bigl(x(\varphi(f_j)-f_j),x(f_j)\bigr)\\
 &\le r_jx(b)=r_jx(\varphi(b)).
 \end{aligned}
\]

The first term is bounded by its norm and `r_j ε ≤ r_j x(b)`;
the second is bounded by the defining inequality of `V`.
This proves that actual seminorm pullback along `φ` preserves membership
in `V`. The numerator threshold uses each actual positive radius,
without replacing the radii by one or imposing a value-group condition.

`locus_image_eq_of_displacement_lt` applies this criterion to both
bounded maps of an automorphism. The bounds for `g.inv` give
`g • V ⊆ V`, because the spectrum action uses the inverse map.
The bounds for `g.hom` put `g⁻¹ • x` in `V` whenever `x ∈ V`;
`g • (g⁻¹ • x) = x` gives the reverse inclusion.
The result is equality of the actual subsets.

`isOpen_locusStabilizer ρ hρ d` derives openness of
`d.locusStabilizer.comap ρ` in `G`. Choose the positive denominator
bound. For each of the finitely many coefficients, norm-continuity
makes its forward displacement smaller than the appropriate positive
threshold near `1`. Inverse orbits are continuous by composing the
forward orbits with continuous group inversion and using `ρ(g⁻¹) =
ρ(g)⁻¹`. At `1` every displacement is zero.
`Filter.eventually_all` combines the finite numerator estimates,
including an empty numerator tuple. The perturbation criterion puts a
neighborhood of `1` inside the full stabilizer preimage.
`Subgroup.isOpen_of_mem_nhds` then proves openness of that subgroup.
In particular, openness is derived from the algebra orbits rather than
assumed as part of a domain-spectral action.

## Open subgroups and finite refinements

`normOpenStabilizer ρ hρ d` bundles the full stabilizer preimage as an
`OpenSubgroup G`; `mem_normOpenStabilizer` is exactly the image-equality
criterion for `ρ g` on `d.locus`.

For a finite set `s` of actual rational charts and a prescribed open
subgroup `U`, `finiteNormOpenStabilizer ρ hρ s U` is

\[
  U\ \cap\!\!\bigcap_{d\in s}\operatorname{normOpenStabilizer}(\rho,h_\rho,d).
\]

`mem_finiteNormOpenStabilizer` identifies membership with membership in
`U` and preservation of every displayed locus. The construction uses
the finite subtype of `s`, so an empty family is allowed and yields `U`.
`finiteNormOpenStabilizer_le` proves containment in `U`.
`finiteNormOpenStabilizer_mono` proves coherence: if `s ⊆ t` and `U ≤ V`,
then the subgroup for `t,U` is contained in the subgroup for `s,V`.
Adding loci or shrinking the prescribed subgroup thus shrinks the
constructed simultaneous stabilizer.

## Actual bounded section operators

The remaining declarations additionally require `CompleteSpace K`.
This is used through the published full representation of a rational
chart by `d.algebra` and `d.baseMap`. `locusStabilizer_toDomain` identifies
the chart's full stabilizer with the stabilizer of the actual
represented domain `d.toDomain`; their locus subsets are definitionally
the same.

`normStabilizerHom ρ hρ d` sends a member of the derived open subgroup
to that represented-domain stabilizer, retaining its original bounded
automorphism `ρ g`. `normSectionAction ρ hρ d` composes this homomorphism
with `DomainAutomorphism.stabilizerSectionAction`. It therefore constructs
an action by actual bounded automorphisms on the whole rational quotient
algebra `d.algebra`, including any nilpotents. The section maps are the
unique bounded factorizations already constructed from full domain
representation, not functions supplied as additional input.

`normSectionAction_baseMap` gives the equation

\[
 \operatorname{normSectionAction}(g).\mathrm{hom}(\operatorname{baseMap}(a))
   =\operatorname{baseMap}(\rho(g).\mathrm{hom}(a)).
\]

For an actual chart arrow `f : d ⟶ e` and a common `g : G` preserving
both loci, `normSectionAction_restriction` proves
`α_d(g).hom.comp f.restriction =
f.restriction.comp α_e(g).hom`.
It applies the published represented-domain restriction theorem to the
actual arrow `(toDomainFunctor K A).map f`; the stored bounded
restriction map is retained.

## Provenance and scope

The perturbation argument adapts the published
`Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerProof`
by Worker 552, using the proof route supplied by Worker 36.
Worker 56 implements the positive-radius thresholds, finite coherent
refinements and represented-domain adapters here. This module is an
internal construction with its proof explained above; it does not claim
to close a separately published proposition target.

The original geometric conventions are in Vladimir Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.4, Example 1.2.2(v), allows arbitrary positive polyradii.
Definitions 1.2.3 and 1.2.5 give the bounded multiplicative spectrum and
evaluation topology; Exercise 1.2.4 gives its normalized norm bound,
and Fact 1.2.6 gives the compact-spectrum context.
Printed/PDF p.9, Definition 2.2.1 and Exercise 2.2.2(ii), give the
affinoid-domain universal property and positive-radius rational
inequalities and quotient. These pages were read directly.
The source uses no common spectral zeros; this module retains the
Library chart's explicit unit-generation hypothesis and does not assert
an equivalence between those conditions.

The original source's analytic setting uses complete coefficient fields.
The stabilizer proof before the represented-domain bridge needs only
the imported compact-spectrum and nonarchimedean results for the actual
normed algebra, so those declarations allow an incomplete field.
The bridge states its completeness hypothesis explicitly. All declarations
permit trivial valuations, arbitrary positive real radii, arbitrary chosen
closed ideals, nonreduced and zero quotient algebras, and empty spectra,
rational loci and finite families whenever the displayed data exist.
No proper-ideal or nonemptiness premise is imposed.

Only the specified rational loci receive the derived open stabilizers.
This module proves no preservation of arbitrary compact or distinguished
domains, continuity of the transported section orbits, comparison with
the full analytic automorphism topology, general analytic or etale site,
or construction of the Harris tower.
