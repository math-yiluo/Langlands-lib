# Integral models over the actual local-field integer ring

This is an internal specialization of the actual integral-model and reduction
interfaces to a nonarchimedean local field. Its source definition is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 2.10.1
and Remark 2.10.2, printed p. 121 / PDF p. 152. The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 25, leave that model definition unchanged.

`LocalFieldIntegralModel F G` is exactly `IntegralModel 𝒪[F] F G`. Here
`F : Type u` has the existing `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F` instances. The
universe `u` is arbitrary. The ring `𝒪[F]` is the actual subring
`(ValuativeRel.valuation F).integer` of elements of valuation at most one.
Mathlib's `NumberTheory.LocalField.Basic` provides its discrete valuation
ring structure and the finiteness of its actual residue field `𝓀[F]`.
The fraction-field instance for a valuation integer subring is supplied by
Mathlib's `RingTheory.Valuation.ValuationRing`. The specialization therefore
requires no chosen surrogate ring or identification with an abstract DVR.
Neither the definition nor any of its maps restricts the characteristic of
`F`; mixed and equal characteristic use these same definitions.

`integerInclusion F` is the subring inclusion `𝒪[F] → F`, with the formula
`x ↦ (x : F)`. `integerInclusion_eq_algebraMap` records that it is the
canonical algebra map used by the integral model. `residueHom F` is exactly
`IsLocalRing.residue 𝒪[F]`, with target the actual quotient field `𝓀[F]`.
These two coefficient maps require only the field and valuative relation.
The base-map equalities identify their contravariant spectrum maps with the
ones in the common generic- and special-fibre constructions.

The local-field namespace exposes abbreviations for the original integral
sections, integral-point map and image, special-fibre group scheme, reduction,
congruence kernel and generic congruence image. They reuse the original
definitions and their group laws. In particular, `specialFibre` retains the
full group scheme over `𝓀[F]`. Both evaluation theorems specialize the already
proved pullback-lift formulas: the generic lift is postcomposed with the
supplied `genericIso`, and the residue lift gives reduction. The coefficient
base-map equalities make the actual inclusion and quotient explicit. The
normality theorem specializes the existing image-normality theorem and names
`integralPoints` as the ambient group.

The connectedness predicates and compatible-model morphisms of the common
interface apply directly to this abbreviation, with their original precise
meanings and hypotheses. Smoothness remains an additional property, and the
model and generic-fibre isomorphism remain supplied data. This module asserts
no model existence, parahoric or fixer identification, reduction surjectivity,
maximal reductive quotient, pro-p property, topology or building certificate.
