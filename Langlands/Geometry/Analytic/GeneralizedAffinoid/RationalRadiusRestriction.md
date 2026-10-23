# Radius restriction of weighted rational quotients

Worker 56 constructed this module from the published weighted series restriction,
closed-relation descent and rational quotient APIs. All public declarations are
in `Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.

## Inputs and direction

Let `K` be an ultrametric normed field and `A : PresentedAffinoidAlgebra K`
an actual closed-ideal quotient with arity `n`, positive polyradius
`r = A.polyradius`, and closed ideal `I = A.ideal`. Fix representatives
`g` and `f j` in `GeneralizedTateAlgebra r K`, where `j : Fin m`.
Choose positive polyradii `s` and `t` on `Fin m` and assume
`hts : ∀ j, t j ≤ s j`. The old presentation, denominator and numerator
representatives remain fixed.

For a new-variable polyradius `s`, write `i_s` for `appendLeft r s K` and
`q_s` for the presentation map of the published rational quotient

\[
 B_s=K\{r^{-1}T,s^{-1}Y\}/
 \overline{\langle i_s(I)\cup\{i_s(g)Y_j-i_s(f_j):j\in\operatorname{Fin}m\}\rangle}.
\]

The construction `radiusMap K A s t hts g f` is a bounded `K`-algebra
homomorphism `B_s → B_t`. It uses the existing quotient carriers and their
actual quotient norms. No coefficient completeness, nontrivial valuation,
value-group restriction on radii, proper-ideal condition, reducedness or
unit-ideal generation is assumed. The old and new arities may each be zero,
and either quotient may be the zero ring.

## Construction and quotient formula

The private `restrictSeries` applies `boundedRestrictRadius` to the combined
polyradii `r.append s` and `r.append t`. The combined inequality follows
from `PositivePolyradius.append_mono` with equality on the old block.
Thus it retains every formal coefficient. Its three private compatibility
lemmas reuse the published append-left square, coordinate formula and Gauss
contraction.

Compose this series restriction with `q_t`. The private lemma
`radius_relations_vanish` checks both parts of the source relation set:

- For `a ∈ I`, restriction takes `i_s(a)` to `i_t(a)`. Its quotient image
  is the target base map applied to the zero class of `a`.
- Restriction preserves multiplication, subtraction and each variable,
  so `i_s(g)Y_j-i_s(f_j)` goes to `i_t(g)Y_j-i_t(f_j)`. This is a defining
  target relation and hence has zero quotient image.

`radiusMap` applies `descendRelations` to that bounded composite. The imported
descent argument uses continuity and the closed kernel of a map into a normed
ring to annihilate the closure of the generated relation ideal. It requires
neither coefficient nor target completeness.

`radiusMap_presentationMap` states the defining formula for every enlarged
series `h`:

\[
 R_{s,t}(q_s(h))=q_t(\operatorname{restrictRadius}_{r\mathbin{\oplus}s,
 r\mathbin{\oplus}t}(h)).
\]

The equality is definitional for this descent construction. It specifies the
map on every quotient class because the presentation map is surjective.

## Norm and algebraic compatibility

`norm_radiusMap_le` proves `‖R_{s,t}(a)‖ ≤ ‖a‖`. The series restriction
and the target quotient projection are both contractions. The proof passes
their composite estimate with constant `1` to `norm_descendRelations_le`,
which preserves that constant for the actual source quotient norm.

`radiusMap_baseMap` proves
`R_{s,t}(baseMap_s(a)) = baseMap_t(a)` for every `a : A`. It chooses a
series representative using surjectivity, then applies the append-left
compatibility. `radiusMap_fraction` proves that each fraction coordinate
at radius `s` maps to the same indexed fraction coordinate at radius `t`,
using preservation of the enlarged coordinate series. The term *fraction*
here refers to the equation `baseMap(ḡ) * fraction_j = baseMap(f̄_j)`;
no inverse of `ḡ` is used.

`radiusMap_self` identifies restriction from `s` to itself with the identity
bounded map. For a further positive polyradius `v` with `v j ≤ t j`,
`radiusMap_trans` proves equality of bounded homomorphisms

\[
 R_{t,v}\circ R_{s,t}=R_{s,v}.
\]

Both proofs use `hom_ext_presentation` and reduce to the published series
restriction identity and composition laws. Proof irrelevance identifies the
proofs of the coordinatewise inequalities used by the two expressions.

## Spectrum map and nested loci

`radiusSpectrumMap` is the actual continuous pullback of bounded multiplicative
seminorms along `radiusMap`, with direction `BanachSpectrum B_t → BanachSpectrum B_s`.
`spectrumMap_radiusSpectrumMap` proves that its composite with the map to
`BanachSpectrum A` equals the target quotient's own map to the base spectrum.
The proof applies spectrum extensionality and `radiusMap_baseMap`.

`locus_mono` proves `locus K A t g f ⊆ locus K A s g f`: for each point
of the smaller locus, multiply `t j ≤ s j` by the nonnegative value of the
base denominator and compose inequalities. This proves containment of the
already defined weighted inequality sets. It makes no claim that either
quotient spectrum maps onto its locus.

## Provenance and scope

The original source context is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Example 1.2.2(v), printed/PDF page 4, supplies the weighted restricted-series
formula and norm. The quotient-norm discussion and Definitions 2.1.1–2.1.2,
page 7, give the affinoid quotient context. Exercise 2.2.2(ii), page 9,
supplies the common-denominator equations `gT_j-f_j` and weighted rational
inequalities.

This module is a derived construction from those formulas and the existing
Library APIs. The source does not separately state this exact fixed-presentation
radius map. The implemented relation and quotient-norm arguments justify the
limited algebraic conclusion without completeness or a no-common-zero
hypothesis. The source's analytic-domain theorem has stronger hypotheses and
is not asserted here. In particular, the module proves neither injectivity,
surjectivity nor isometry of the quotient restriction, nor analytic-domain
representability, reverse spectrum containment, comparison with relative
series over `A`, or independence from arbitrary base presentations.
