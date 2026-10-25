# Smooth algebras over a domain are reduced

Worker 129 authored the Lean proof. Worker 428 checked the implementation and
prepared this paired documentation for the prerequisite of the field global
functions proof.

`isReduced_of_etale_of_domain` embeds an etale algebra over a domain into its
tensor product with the fraction field. Etale algebras are flat, so
`Algebra.TensorProduct.includeRight_injective` makes this map injective.
The base change is formally unramified over a field, hence reduced by
`Algebra.FormallyUnramified.isReduced_of_field`. Reducedness descends through
the injection.

`isReduced_of_smooth_of_domain` tests a nilpotent element in every maximal
localization. At each such ideal, the smooth algebra has a standard etale
polynomial chart by
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`. The polynomial
ring over the domain is a domain, so the first lemma makes the chart reduced.
The nilpotent vanishes in this principal localization. Its localization
element is invertible in the chosen maximal localization, so the universal
map from the principal localization shows that the element also vanishes
there. `eq_zero_of_localization` then gives vanishing in the original ring.

`isReduced_of_smooth_over_field` uses the affine cover of a smooth scheme
over a field. Each affine chart has a smooth section algebra over the field:
the canonical `Scheme.ΓSpecIso` identifies the base global sections with
the field, and the section map of the smooth morphism is smooth. The ring
result makes each chart reduced, hence the scheme is reduced.

`geometricallyReduced_of_smooth` applies that scheme result to every
field-valued pullback of an arbitrary smooth morphism. Smoothness is stable
under base change, so each such pullback has reduced source, which is exactly
Mathlib's `GeometricallyReduced` condition. The scheme lemmas are uniform in
the arbitrary universe `u`; the ring lemmas allow independent universes for
the base ring and algebra. No properness, noetherian, characteristic,
connectedness or nonemptiness hypothesis is used.

The field consequence agrees with the reducedness part of Stacks Project
Tag 056T, Lemma 33.25.4, retained as `056T.html` in registered source
`stacks-global-functions-field-and-fibre-criterion-2026-10-23` (directory
SHA256 `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`).
The ring-level domain statement and the fraction-field argument are internal
prerequisites derived from the named Mathlib results. The implemented proof
does not pass through regularity or normality and claims neither conclusion.
