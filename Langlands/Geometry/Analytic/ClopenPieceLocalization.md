# Restrictions to clopen pieces are localizations at idempotents

Author: Worker 36.

This module shows that the Weierstrass chart of a clopen subset of an affinoid
spectrum is the localization of the algebra away from the idempotent of the
subset. It follows that the restriction from a recognized subset to a
recognized piece cut out of it by an open set is flat, surjective and finite.
In particular this restriction is flat and unramified at every point of its
spectrum. This is the algebraic input needed to compare the pointwise
conditions of `AffinoidPointwiseEtale` on a finite piece and on a smaller
piece, as in Berkovich's composition results for flat and étale morphisms.

## Original source and derived provenance

The source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
PDF SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Theorem 7.4.1 (Shilov Idempotent Theorem), printed p.135 / PDF p.149,
describes clopen subsets of the spectrum by idempotents. Corollary 7.4.2,
printed p.136 / PDF p.150, relates idempotents to decompositions of the
algebra as a direct product and to connectedness of the spectrum. The
statement that a clopen piece is the localization away from its idempotent,
with the resulting flatness and surjectivity, is derived here. It is the form
in which the splitting is used in Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`: the proof
of Lemma 3.1.2, printed pp.54–55 / PDF pp.51–52, and Corollaries 3.2.6 and
3.3.8, printed pp.59 and 63 / PDF pp.56 and 60, which assert that flat and
étale morphisms compose.

## Idempotents with constant values

- `idempotent_eq_one_of_forall`: an idempotent taking the value `1` at every
  point is `1`.
- `idempotent_eq_zero_of_forall`: an idempotent vanishing at every point is
  `0`.

Both apply the uniqueness of `AffinoidIdempotents` to the clopen sets
`univ` and `∅`.

## The Weierstrass chart of a clopen set

Let `B` be a presented affinoid algebra, `C` a clopen subset of its spectrum,
`e = clopenIdempotent C` and `d = clopenRationalChart C`.

- `comap_mem_of_clopenRationalChart`: every point of the spectrum of the
  chart algebra pulls back into `C`, since the chart represents `C`.
- `baseMap_clopenIdempotent`: `d.baseMap e = 1`. The image is idempotent and
  takes the value `1` at every point.
- `baseMap_compl_clopenIdempotent`: `e` becomes `0` on the Weierstrass chart
  of the complement.
- `clopenCover C hC` is the two-member finite cover of the whole spectrum by
  the Weierstrass charts of `C` and of its complement.
- `clopenIdempotent_mul_eq_zero`: if `d.baseMap a = 0`, then `e * a = 0`.
  Both restrictions of `e * a` vanish, and restrictions along the cover
  detect equality (`Domain.FiniteCover.algebra_ext_of_restrict_eq`).
- `isLocalization_clopenRationalChart`: with `d.algebra` a `B`-algebra
  through `d.baseMap`, it is the localization of `B` away from `e`. Powers of
  `e` map to `1`. Every element has a preimage, by
  `exists_lift_clopenRationalChart` of `FiniteMorphismSmallNeighborhoods`. If
  `a` and `b` have the same image, then `e a = e b` by the previous item.
- `flat_clopenRationalChart`: hence `d.baseMap` is flat (Mathlib's
  `IsLocalization.flat`).

## Clopen pieces of recognized subsets

Let `Q` and `P` be recognized subsets of the full recognition of an atlas,
with `Q.locus ⊆ P.locus`.

- `isClopen_chart_preimage_of_eq_inter`: if `Q.locus = P.locus ∩ O` for an
  open `O`, the preimage of `Q.locus` under the chart of `P` is clopen. It is
  the preimage of `O`, hence open. It is compact, because the chart is an
  embedding and the image of the preimage is the compact locus of `Q`. Hence it
  is closed.
- `restriction_flat_and_surjective`: suppose the preimage of `Q.locus` is
  clopen. Then the restriction from `P` to `Q` is flat and surjective. It
  represents the same set as the Weierstrass chart `d` of that preimage. The
  universal properties give `ψ₁ ∘ d.baseMap = restriction` and
  `ψ₂ ∘ restriction = d.baseMap`, and uniqueness gives `ψ₁ ∘ ψ₂ = id` and
  `ψ₂ ∘ ψ₁ = id`. So the restriction is a localization followed by a bijection,
  hence flat. It is surjective because `d.baseMap` is surjective.
- `restriction_isEtaleAtPoint`: the restriction is flat and unramified at
  every point. Surjective maps are formally unramified.
- `restriction_finite`: the restriction is finite as a ring map.

## Scope

General Banach algebras, the product decomposition of Corollary 7.4.2, and the
composition of flat, unramified and étale morphisms themselves are not
treated here.
