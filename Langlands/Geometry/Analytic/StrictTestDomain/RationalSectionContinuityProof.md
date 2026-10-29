# Continuous section orbits on an invariant rational quotient

Author: Worker 474.

The theorem
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.rationalSectionOrbitContinuity`
proves the exact published proposition
`RationalSectionOrbitContinuityStatement.{u,v}`. It imports the statement and
its action constructions without modifying them. The field occupies universe
`u` and the topological group occupies the independent universe `v`.

Let `K` be a complete ultrametric normed field, `P` an actual presented
strict affinoid algebra, and `d : RationalData K P` a unit-radius rational
presentation. For an algebraic homomorphism `ρ : G →* locusStabilizer d`,
continuity of every forward base orbit `g ↦ (ρ g).hom(a)` implies continuity
of every fixed-quotient section orbit
`g ↦ (stabilizerSectionAction d (ρ g)).hom(b)`. The section topology is the
constructed quotient norm topology on `d.algebra`.

## Implemented proof

The proof implements the internal route described in the published target's
Markdown, authored by Worker 36. Its auxiliary theorems are derived from the
existing Tate-series, quotient-norm and rational-localization constructions.
They do not assume the conclusion or a common bound on the operators.

1. **Contractivity from the coordinates.** In namespace
   `PresentedStrictAffinoidAlgebra`, `norm_map_le_of_coordinates` shows that a
   bounded map between actual presentations is contractive if each coordinate
   image has norm at most one. If the target is a subsingleton, its norm is
   zero and the estimate follows directly. Otherwise
   `quotient_norm_one_le` (now imported from
   [AffinoidUnitNorm](../AffinoidUnitNorm.md)) and `one_le_norm_one` supply a local `NormOneClass`
   instance on the target. Composing with the source's Tate projection,
   `map_eq_evaluate` and `evaluate_norm_le` bound the image of every Tate
   representative by its Gauss norm. `exists_representative_norm_lt` then
   passes the estimate to the infimum defining the quotient norm. This uses
   no nontrivial-valuation or open-mapping assumption.

2. **One neighborhood for every section.**
   `eventually_coordinates_norm_le` considers any continuous finite tuple
   `c(t,i)` whose values at `x` have norm at most one. For each coordinate,
   continuity makes `‖c(t,i) - c(x,i)‖ < 1` locally. The ultrametric inequality
   gives `‖c(t,i)‖ ≤ max(‖c(t,i) - c(x,i)‖, ‖c(x,i)‖) ≤ 1`.
   Finite intersection gives a single neighborhood for the whole tuple.
   Applying the preceding estimate,
   `eventually_contractive_of_coordinates` derives
   `∀ᶠ t in 𝓝 x, ∀ a, ‖φ(t)(a)‖ ≤ ‖a‖`. The quantifier over all sections
   lies inside one common neighborhood; separate boundedness of each map
   would not supply this conclusion.

3. **Approximation of arbitrary sections.**
   `continuousAt_map_monomial` expresses a mapped Tate monomial as a constant
   scalar times a finite product of powers of the coordinate images.
   `continuousAt_map_partial_sum` then handles finite sums.
   `exists_partial_sum_approx` uses surjectivity of the quotient projection,
   convergence of the monomial expansion of a Tate series, and contractivity
   of the quotient projection to approximate any quotient section.
   For `b` and a positive `ε`, `continuousAt_map_of_coordinates` chooses a
   finite sum image `q` with `‖b-q‖ < ε/3`. The common local contraction
   bounds `dist(φ(t)(b), φ(t)(q))`; the same coordinate bound at `x` bounds
   `dist(φ(x)(q), φ(x)(b))`. Continuity of the finite sum bounds the middle
   distance by `ε/3`. The triangle inequality proves continuity of the
   orbit of `b` at `x`.

4. **The rational presentation coordinates.** In namespace
   `StrictTestDomain.RationalData`, `isUnit_map_denominator` maps the unit
   `d.baseMap(d.denominator)` through any bounded map. Its invertibility is
   the existing rational-localization theorem applied to
   `d.generatesUnitIdeal`. Applying a map to the fraction equation and
   cancelling this unit gives `map_fraction_eq_inverse_mul`:

   `φ(d.fraction(j)) = Ring.inverse(φ(d.baseMap(d.denominator))) * φ(d.baseMap(d.numerator(j)))`.

   Mathlib's `NormedRing.inverse_continuousAt` at a unit, composed with the
   denominator orbit, proves `continuousAt_map_fraction` from continuity
   on base sections. It applies to the complete presented quotient even
   when it is the zero ring. For an old coordinate,
   `baseMap_model_coordinate` supplies an actual base preimage using
   `RationalLocalization.modelEquiv` and the existing
   `RationalPresentation.baseMap_coordinate`. Splitting a quotient index
   with `Fin.addCases`, `continuousAt_map_coordinates` therefore gives
   continuity on all old and new coordinates. Empty coordinate types
   require no special hypothesis.

5. **Continuity at the identity.**
   `continuous_section_baseMap` uses
   `stabilizerSectionAction_baseMap`: the section orbit of a base section
   is the given base orbit composed with the continuous bounded structural
   map. The preceding rational-coordinate lemma supplies continuity on
   every presentation coordinate. At the identity the section map is the
   identity, and `coordinate_norm_le_one` bounds its coordinate images by
   the quotient projection of Tate variables of Gauss norm one.
   `continuousAt_section_one` now applies the general approximation lemma.
   This step uses only a topological space structure on `G`; continuity
   of group operations is used in the next step.

6. **Group translation.**
   `continuous_map_of_continuousAt_one` is a reusable lemma for any
   multiplicative family of bounded endomorphisms. At `g₀`, the map
   `g ↦ g₀⁻¹*g` tends to the identity. Compose continuity of the orbit
   there with the fixed continuous bounded map `φ(g₀)`. The action law
   rewrites `φ(g₀)(φ(g₀⁻¹*g)(b))` as `φ(g)(b)`; multiplicativity also
   identifies the central value. No topology on the space of operators
   is needed. `continuous_section_orbit` instantiates this lemma using
   `stabilizerSectionMap_mul`, with the right factor applied first.
   The closing theorem introduces the exact target's parameters and
   applies `continuous_section_orbit`.

The stabilizer preserves the actual rational subset setwise; it need not
preserve its chosen presentation or fix any individual point. The proof
adds no nontrivial valuation, nonzero quotient, reducedness, nonempty locus,
positive numerator arity or local compactness hypothesis. All common bounds
are local and derived; a bound on the entire group is not asserted.

## Sources and scope

The underlying quotient norm and strict affinoid presentations are described
in Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
section 2.1 and Definition 2.1.2, printed/PDF p. 7. Definition 2.1.11, p. 8,
uses bounded homomorphisms. Definition 2.2.1 and Exercise 2.2.2(ii), p. 9,
give affinoid domains and the rational quotient equations `g*T_j=f_j`.
Registered source: `berkovich-2009-trieste-analytic-spaces`; PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The present local continuity criterion and its auxiliary lemmas are internal
derivations from the Library constructions, not a numbered theorem quoted
from those lectures.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic spaces*
(1995–1996), section 1.1, printed/PDF pp. 1–2, motivates continuity on local
functions through compact analytic domains, finite sets of functions and
spectral bounds. Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

This module proves quotient-norm continuity on one invariant rational
quotient. It does not identify that norm with a spectral norm, construct or
identify the full analytic automorphism topology, prove stabilizer openness
or smoothness, or construct an equivariant etale site. These are separate
questions from the exact proposition proved here.
