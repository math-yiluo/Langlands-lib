# Coefficient and radius maps of intrinsic weighted rational quotients

Author: Worker 56. The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation`.
This module specializes the published relative closed-equation quotient
transport and radius restriction to the actual rational equations. It constructs
their compatibility from the input coefficient map and radii.

## Objects and hypotheses

Let K be an ultrametric normed field, let A, B and C be actual
`PresentedAffinoidAlgebra K` objects, and fix `m : ℕ`, a positive polyradius
`s : PositivePolyradius (Fin m)`, `g : A` and `f : Fin m → A`. Write

\[
R_s(A;g,f)=
A\{s^{-1}Y\}/
\overline{\operatorname{span}_{\mathrm{ideal}}
  \{C(g)Y_j-C(f_j):j\in\operatorname{Fin}(m)\}}.
\]

This is the imported `Algebra K A s g f`, with its actual quotient norm.
The imported `quotientMap`, `baseMap` and `fraction` are respectively the
relative series projection, its restriction to constant series, and the images
of the new variables. The elements g and f are elements of A itself, so the
construction makes no choice of scalar-series representatives for them.

## Bounded coefficient maps

For every `φ : BoundedAlgHom K A B`, `mapCoefficients_equations` proves
that coefficientwise application of φ sends each source rational generator
to the correspondingly labelled target generator. It uses preservation of
subtraction, multiplication, constant series and variables. The published
closed-ideal descent then constructs

\[
T_s(\varphi):R_s(A;g,f)\longrightarrow
R_s(B;\varphi(g),\varphi\circ f),
\]

named `transport`. There is no separate relation-compatibility hypothesis.
The underlying coefficientwise map and its descent are actual bounded
K-algebra homomorphisms.

`transport_quotientMap` identifies the map on every series representative.
`transport_baseMap` sends the coefficient a to φ(a), and
`transport_fraction` preserves each labelled new fraction. `eq_transport`
proves that these coefficient and fraction formulas determine the bounded map.
It applies the imported rational `hom_ext`, which uses relative-series
extensionality and quotient surjectivity.

For every real `c ≥ 0` satisfying `‖φ a‖ ≤ c * ‖a‖` for all a,
`norm_transport_le` proves the same bound on these quotient norms.
`norm_transport_le_of_contractive` gives the constant-one case. These follow
from the published relative quotient transport bounds, including their
zero-constant endpoint. `transport_id` and `transport_comp` give identity and
composition as equalities of bounded algebra maps with the corresponding
mapped rational data.

## Continuous coefficient pullbacks

The imported rational inequality locus is

\[
L_s(A;g,f)=
\{x\in\mathcal M(A):x(f_j)\leq s_jx(g)\text{ for every }j\}.
\]

`spectrumTransport` is the continuous contravariant pullback on the genuine
quotient spectra induced by `transport`. Its evaluation formula is
`spectrumTransport ... x a = x (transport ... a)`.
`locusTransport` restricts coefficient-spectrum pullback to
`L_s(B;φ(g),φ∘f) → L_s(A;g,f)`. Evaluating the pulled-back seminorm at a
gives `x (φ a)`; this makes the required inequalities precisely those of the
input point.

The imported `spectrumToLocus` is the forward continuous map obtained by
restricting quotient seminorms along `baseMap`. The equality
`spectrumToLocus_transport` proves its naturality as an equality of continuous
maps. The proof evaluates both sides at each coefficient and applies
`transport_baseMap`.

## Smaller radii

Let `t : PositivePolyradius (Fin m)` satisfy `hts : ∀ j, t j ≤ s j`.
The published series restriction retains every formal coefficient.
`restrictRadius_equations` proves that it preserves the rational generators,
using its constant-series and variable formulas. Closed-ideal descent constructs

\[
\rho_{s,t}:R_s(A;g,f)\longrightarrow R_t(A;g,f),
\]

named `radiusMap`. It requires only the coordinatewise radius inequality.
`radiusMap_quotientMap` is its representative formula,
`radiusMap_baseMap` fixes every coefficient, and `radiusMap_fraction`
preserves each labelled fraction. `norm_radiusMap_le` proves contraction.
`eq_radiusMap` characterizes this map by its coefficient and fraction images.

`radiusMap_self` proves the identity at equal radii, and `radiusMap_trans`
proves `ρ(t,q) ∘ ρ(s,t) = ρ(s,q)` for every `q ≤ t ≤ s`.
`radiusMap_transport` proves

\[
\rho_{B,s,t}\circ T_s(\varphi)
 =T_t(\varphi)\circ\rho_{A,s,t}.
\]

Each proof applies the imported coefficient/fraction extensionality and the
corresponding image formulas.

`radiusSpectrumMap` is the continuous contravariant quotient-spectrum pullback.
Its evaluation formula applies the point to `radiusMap ... a`.
`locusRadiusMap` sends `L_t(A;g,f)` into `L_s(A;g,f)` by retaining its underlying
point of `𝓜(A)`. Membership follows from `t_j ≤ s_j` and nonnegativity of
`x(g)`. `spectrumToLocus_radiusMap` proves naturality of the forward structural
maps using the coefficient formula. `radiusSpectrumMap_spectrumTransport`
proves the reversed coefficient/radius square on quotient spectra by evaluating
the algebra square. `locusRadiusMap_locusTransport` proves the same commuting
square on rational inequality loci by equality of the underlying pulled-back
seminorms.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), source `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The retained file is
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
Printed/PDF page 8, Definition 2.1.6(i), gives the relative weighted restricted
series convention, and Definition 2.1.11 describes the dual category with
bounded algebra homomorphisms. Page 9, Exercise 2.2.2(ii), gives the rational
equations and inequalities. These pages were read directly. The coefficient
and radius maps, norm bounds, uniqueness and commuting squares here are derived
infrastructure from the published concrete relative-series and quotient APIs;
they are not asserted to be a verbatim theorem of those passages.

All finite variable blocks, including the empty block, and all positive real
radii are permitted. Completeness of K, a nontrivial valuation, a unit-ideal or
no-common-zero condition on the rational data, and a nonzero quotient are not
required for these constructions. The source's analytic-domain assertion has
additional hypotheses. This module constructs bounded quotient maps and
continuous pullbacks and their stated laws. It does not prove denominator
invertibility, a reverse map from the inequality locus, injectivity or
surjectivity of the structural spectrum map, a scalar-presentation comparison,
arbitrary presentation independence, or an analytic-domain, sheaf or site
construction.
