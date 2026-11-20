# Proof that real-radius binary Laurent splits of full domains are split squares

`Langlands.Analytic.PresentedAffinoidAlgebra.domainBinaryLaurentSplitSquare`
proves `DomainBinaryLaurentSplitSquareStatement`. The only axioms it uses are
`propext`, `Classical.choice` and `Quot.sound`.

## Overview

Fix `K`, `R`, a full domain `U`, an element `a ∈ U.algebra` and a real radius
`ρ > 0`. Choose a series `a₀` with `presentationMap a₀ = a`. Three rational
charts over `U.algebra` describe the binary Laurent split. Each has arbitrary
real radii, so no scalar of prescribed absolute value is needed:

- `chart₁`: denominator `1`, numerator `a₀`, radius `ρ`. Its locus is `{|a| ≤ ρ}`.
- `chart₂`: denominator `a₀`, numerator `1`, radius `ρ⁻¹`. Its locus is
  `{1 ≤ ρ⁻¹|a|} = {|a| ≥ ρ}`.
- `chart₁₂`: denominator `a₀`, numerators `1, a₀²`, radii `ρ⁻¹, ρ`. Its locus is
  `{1 ≤ ρ⁻¹|a|, |a|² ≤ ρ|a|} = {|a| = ρ}`, the intersection of the other two.

In each chart the denominator and numerators generate the unit ideal: the
denominator `1` is a unit, and in the other two charts the numerator `1` is.

The existence part of the statement uses the extended chart domains
`U.extend (chart₁ …).toDomain` and `U.extend (chart₂ …).toDomain`. For the
split-square part, take arbitrary full domains `U₁`, `U₂`, `W` with the
prescribed loci. Each is compared with the relative rational quotient of its
chart over `U.algebra`. The comparisons identify the original restrictions
from `U` with the coefficient maps. The split-square properties are proved for
the model quotients and then transported back with
`BoundedAlgHom.SplitSquare.congr`. Gluing does not come from the model: it is
the Library's finite-cover algebra gluing applied to the two-member cover
`{U₁, U₂}` of `U`.

## Analytic helpers

- `exists_eq_of_approx`: let `T : V →+ W` be continuous, with `V` complete.
  Suppose every `w` has some `v` with `‖v‖ ≤ C‖w‖` and `‖w − T v‖ ≤ ‖w‖/2`.
  Then every `w` equals `T v` for some `v` with `‖v‖ ≤ 2C‖w‖`. The proof
  iterates the residual map `z ↦ z − T(f z)`. The `k`-th residual has norm at
  most `‖w‖ 2⁻ᵏ`, so the corrections form an absolutely summable series of total
  norm at most `2C‖w‖`. The images of the partial sums are `w` minus the
  residuals, which tend to `w`.
- `norm_mul_pow_le`: `‖x yⁿ‖ ≤ ‖x‖ ‖y‖ⁿ` in a normed ring, with no assumption
  on `‖1‖`.

## The model computation

Sections `Relative`, `Core`, `Pieces` and `Split` work over an arbitrary
presented affinoid algebra `A` and `a ∈ A`. They use the intrinsic relative
rational quotients `RelativeRationalPresentation.Algebra K A s g f`: the
generalized Tate algebra over `A` modulo the closed ideal of the equations
`g Xⱼ − fⱼ`. Write `baseMap` for the coefficient map and `Fⱼ` for the class of
`Xⱼ`. The data are

- side 1: one variable, radius `ρ`, `g₁ = 1`, `f₁ 0 = a`;
- side 2: one variable, radius `ρ⁻¹`, `g₂ = a`, `f₂ 0 = 1`;
- overlap: two variables, radii `(ρ⁻¹, ρ)`, `g = a`, `f = (1, a²)`.

These are passed to the lemmas as equations on the parameters, so the same
lemmas apply to the chart data in the domain section.

Identities (section `Core`, from `fraction_equation`):

- `fraction_eq_of_one`: on side 1, `F = a`.
- `baseMap_mul_fraction_of_one`: on side 2, `a F = 1`.
- `overlap_mul_fraction_zero`: on the overlap, `a F₀ = 1`.
- `overlap_fraction_one`: on the overlap, `F₁ = a`, since
  `F₁ = (a F₀) F₁ = F₀ (a F₁) = F₀ a² = a`.

Monomials and weights (section `Relative`):

- `quotientMap_monomial`: the relative monomial with exponent `d` and
  coefficient `c` maps to `c F₀^{d 0} F₁^{d 1}` in the overlap.
- `weight_eq`, `weight_eq_of_le`, `weight_eq_of_lt`: for radii `(ρ⁻¹, ρ)` the
  weight of `d` is `ρ⁻¹^{d 0} ρ^{d 1}`. This equals `ρ^{d 1 − d 0}` if
  `d 0 ≤ d 1` and `ρ⁻¹^{d 0 − d 1}` otherwise.

Pieces (section `Pieces`): the monomial `(d, c)` is assigned to one side.

- `firstPiece d c = c F^{d 1 − d 0}` on side 1 if `d 0 ≤ d 1`, and `0` otherwise.
- `secondPiece d c = c F^{d 0 − d 1}` on side 2 if `d 1 < d 0`, and `0` otherwise.

Section `Split` takes arbitrary bounded algebra maps `t₁`, `t₂` from the two
sides to the overlap that fix coefficients (`tᵢ (baseMap c) = baseMap c`).

- `first_apply`: `t₁ (c Fᵏ) = c aᵏ`.
- `second_fraction`: `t₂ F = F₀`, because both are inverses of `a` in the
  overlap. `second_apply`: `t₂ (c Fᵏ) = c F₀ᵏ`.
- `piece_sum`: `t₁ (firstPiece d c) + t₂ (secondPiece d c)` is the image of the
  monomial `(d, c)`. If `d 0 ≤ d 1` this is `c a^{d 1 − d 0} = c F₀^{d 0} a^{d 1}`.
  Otherwise it is `c F₀^{d 0 − d 1} = c F₀^{d 0} a^{d 1}`. Both use `a F₀ = 1`.
- `norm_firstPiece_le`, `norm_secondPiece_le`: each piece has norm at most
  `‖c‖ · weight(d)`. This uses `norm_baseMap_le`, the radius bound
  `norm_fraction_le` and `norm_mul_pow_le`.
- `exists_approx`: let `h ≠ 0` be in the overlap. Choose a representative `H`
  with `‖H‖ < 2‖h‖` (`exists_representative_norm_lt`). Truncate its monomial
  expansion (`hasSum_monomials`) to a finite set `S` with `‖H − H_S‖ < ‖h‖/2`.
  Take the sums over `S` of the first and second pieces of the coefficients of
  `H`. By the ultrametric inequality and `weighted_norm_coeff_le`, each sum has
  norm at most `‖H‖ ≤ 2‖h‖`. By `piece_sum` the residual is the image of
  `H − H_S`, of norm `< ‖h‖/2` (`norm_quotientMap_le`).
- `exists_split` (needs `CompleteSpace K`): apply `exists_eq_of_approx` with
  `C = 2` to `(v₁, v₂) ↦ t₁ v₁ + t₂ v₂` on the product of the two sides, which
  is complete. Every overlap element `h` is `t₁ v₁ + t₂ v₂` with
  `‖vᵢ‖ ≤ 4‖h‖`.
- `denseRange_second`: the image of each monomial,
  `c F₀^{d 0} F₁^{d 1} = t₂ (c F^{d 0} a^{d 1})`, lies in the range of `t₂`.
  Every overlap element is the image of a series, and the images of its finite
  truncations converge to it. So `t₂` has dense range.

## The domain level (section `Domain`)

- `chartEquiv U c V h`: let `c` be a rational chart over `U.algebra` and `V` a
  full domain with the locus of `U.extend c.toDomain`. Then `V.algebra` is
  boundedly equivalent to the relative rational quotient of `c`. The
  equivalence is `Domain.boundedEquivOfLocusEq` followed by
  `RationalPresentation.relativeEquiv`.
- `chartEquiv_restriction`: this equivalence sends the original restriction of
  `x ∈ U.algebra` to `baseMap x`. The proof uses `restriction_comp`,
  `restriction_eq` for the inclusion `U.extendInclusion` and
  `relativeEquiv_baseMap`.
- `exists_glue`: suppose `U₁, U₂ ⊆ U` cover `U`, `U₁ ∩ U₂ ⊆ W` and
  `W ⊆ U₁, U₂`. Then elements of `U₁.algebra` and `U₂.algebra` with equal
  restrictions to `W` glue to an element of `U.algebra`. The proof builds the
  two-member `Domain.FiniteCover` with members `U₁`, `U₂`. Every domain inside
  both members lies in `W`, so the pair is `AlgebraCompatible`; this uses
  `restriction_comp` and uniqueness of inclusions. Then
  `FiniteCover.algebra_existsUnique` gives the element.
- `chart₁`, `chart₂`, `chart₁₂` are the charts above.
  `chart₁_locus`, `chart₂_locus` and `chart₁₂_locus` compute their loci in the
  spectrum of `U.algebra`. For `chart₁₂` the conditions `ρ ≤ |a|` and
  `|a|² ≤ ρ|a|` together say `|a| = ρ`.
  `extend_chart₁_locus`, `extend_chart₂_locus` and `extend_chart₁₂_locus` give
  the loci of the extended domains in the spectrum of `R`. These use
  `Domain.extend_locus`, `RationalChart.toDomain_locus` and injectivity of
  `U.spectrumMap`, which turns the image of an intersection into an
  intersection of images.
- `splitSquare`: let `e₁`, `e₂`, `e₁₂` be the chart equivalences of `U₁`, `U₂`
  and `W`. Put `t₁ = e₁₂ ∘ restriction ∘ e₁⁻¹` and
  `t₂ = e₁₂ ∘ restriction ∘ e₂⁻¹`. By `chartEquiv_restriction` and
  `restriction_comp` they fix coefficients. The model square on the maps
  `e₁ ∘ restriction`, `e₂ ∘ restriction`, `t₁` and `t₂` is a split square:
  - it commutes because both paths send `x` to `baseMap x`;
  - gluing is `exists_glue`. The cover property `U ⊆ U₁ ∪ U₂` holds because
    every point of `U.locus` comes from a spectrum point `y` of `U.algebra`
    (`spectrumToLocus_surjective`), and `y a ≤ ρ` or `ρ ≤ y a`;
  - density is `denseRange_second`;
  - the splitting, with constant `4`, is `exists_split`.

  `SplitSquare.congr` then transports this square to the four original
  restrictions. It uses the identity equivalence on `U.algebra` and `e₁`, `e₂`,
  `e₁₂` on the other corners. The splitting constant of the result is `4`
  multiplied by bounds of these equivalences. The statement asserts only
  existence of a split square.

## Main theorem

`domainBinaryLaurentSplitSquare` chooses `a₀` with `presentationMap a₀ = a`
(`presentationMap_surjective`). It proves the existence part with the extended
chart domains of `chart₁` and `chart₂` and their loci. It proves the split-square
part with `splitSquare`.

## Provenance

This proof is an internal derivation. The model computation is a real-radius,
norm-controlled version of the direct computation for the covering
`{|f| ≤ 1} ∪ {|f| ≥ 1}` in Piotr Achinger, *Introduction to non-Archimedean
Geometry*, lecture notes, November 22, 2020, §7.1, Proposition 7.1.1, p.64
(registered source `achinger-2020-non-archimedean-geometry-nov22`). That proof
splits a Laurent series in `A⟨X, X⁻¹⟩` into its nonnegative and negative parts.

The implementation differs from that proof as follows.

- Radii are arbitrary positive reals.
- The overlap `{|a| = ρ}` is presented with denominator `a` and numerators
  `1, a²`, in two variables, instead of as a quotient of `A⟨X, X⁻¹⟩`.
- An element is split only approximately, from a finite truncation of a
  representative. The exact splitting with constant `4` comes from iteration
  and completeness (`exists_eq_of_approx`).
- Gluing is not derived from the exact sequence. It is the Library's algebra
  gluing for finite covers of full domains (`DomainAlgebraGluing`).

The Library proves a radius-one analogue for its abstract binary Laurent
diagram (`BinaryLaurentIdealDescent`, splitting constant `2`). This proof does
not use that result. It uses only `BoundedAlgHom.SplitSquare.congr` from
`StrictTestDomain.BinaryLaurentIdealDescent`. Other Library inputs are the
intrinsic relative rational quotients (`RelativeRationalPresentation`), the
comparison `RationalPresentation.relativeEquiv` (`RelativeRationalComparison`),
`Domain.boundedEquivOfLocusEq` (`DomainComparison`), the monomial expansion of
generalized Tate series (`GeneralizedTateAlgebra.hasSum_monomials`), and the
restriction API of `FiniteAffinoidAlgebraDescent.LocalData`.
