# Unit-radius polynomial-locus charts over a trivially normed field

This module adds general facts about the Library's polynomial-locus charts
`PolynomialLocus.chart P r` (module `PolynomialLocusCharts`) in the special case of
unit radii over a trivially normed ground field. All declarations are in the
namespace `Langlands.Analytic.PolynomialLocus`. The counterexample in
`GroundFieldExtensionCounterexample/` uses them to realize finite algebras over
`F₂` as presented affinoid algebras and to construct bounded maps between them.

## Provenance

These are internal lemmas about Library constructions and have no separate
literature source. The fact behind them is elementary. If every nonzero scalar
has norm `1`, the weighted norm of a unit-radius Tate series is the supremum of
`1` over its nonzero coefficients. A convergent series therefore has only finitely
many nonzero coefficients, which makes it a polynomial.

## Hypotheses

`K` is a normed field with `IsUltrametricDist K`. Most results also assume
`hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1`, which says that the norm of `K` is trivial.
`K` is not assumed complete. `A` is a commutative `K`-algebra and
`P : FinitePolynomialPresentation K A` is a finite polynomial presentation of it.
Every result uses the unit polyradius `PositivePolyradius.unit`.

## Unit-radius Tate series

For an arbitrary index type `σ`:

- `tate_norm_le_one hK f`: every unit-radius weighted Tate series `f` has norm at
  most `1`. Every weighted coefficient norm is `0` or `1`, so this follows from
  `GeneralizedTateAlgebra.norm_le_iff`.
- `tate_eq_zero_of_norm_lt_one hK f hf`: if `‖f‖ < 1` then `f = 0`. Each
  coefficient's norm is at most `‖f‖ < 1` (`weighted_norm_coeff_le`), so each
  coefficient is zero.
- `tate_polynomialMap_surjective hK`: the inclusion of polynomials
  `GeneralizedTateAlgebra.polynomialMap` is surjective. Polynomials are dense
  (`denseRange_polynomialMap`), so some polynomial lies within distance `1` of
  `f`. Their difference has norm less than `1` and therefore vanishes.

## The unit-radius chart of a finite presentation

`algebraMap P r : A →ₐ[K] chart P r` is the Library's algebra map from `A` to
the chart. For `r` the unit polyradius:

- `algebraMap_surjective P hK`: `algebraMap P` is surjective. Every element of
  the chart is the class of a Tate series. That series is a polynomial `p`, and
  its class is `algebraMap P (P.map p)`.
- `norm_le_one P hK s`: every element `s` of the chart has quotient norm at most
  `1`.
- `eq_zero_of_norm_lt_one P hK s hs`: an element of quotient norm less than `1`
  is zero. It has a representative series of norm less than `1`
  (`exists_representative_norm_lt`), and that series is zero.

So over a trivially normed field, `algebraMap P` maps `A` onto the unit-radius
chart. Together, the last two lemmas say that every nonzero element of the
chart has norm exactly `1`; this combination is not stated as a separate lemma.

## Bounded maps out of the chart

Let `B` be a normed commutative ring with `NormedAlgebra K B`.

- `comp_map_eq_aeval P g`: for a `K`-algebra map `g : A →ₐ[K] B`, the composite
  `g ∘ P.map` is polynomial evaluation at the images `g (P.map (X i))` of the
  presentation variables.
- `hasBoundedMonomials_of_norm_le_one P g hg`: if `‖g a‖ ≤ 1` for every `a`, then
  these images have unit-weight bounded monomials with constant `1`. Each
  monomial value is `g` of an element of `A`.

Assume moreover that `B` is ultrametric and complete.

- `evaluate_polynomialMap P b hb p`: weighted evaluation at `b` of the Tate
  series of a polynomial `p` equals `MvPolynomial.aeval b p`.
- `lift P g hg : BoundedAlgHom K (chart P unit) B` is the bounded map induced by
  `g`. It is the Library's `evaluateRelations` at `b i = g (P.map (X i))`. Every
  defining relation of the chart is the image of a polynomial `p` with
  `P.map p = 0`, and evaluation sends it to `g (P.map p) = 0`.
- `lift_algebraMap P g hg a`: `lift P g hg (algebraMap P unit a) = g a`.

Finally, without assuming `NormedAlgebra K B` (only `Algebra K B`):

- `hom_ext P hK φ ψ h`: two bounded `K`-algebra maps out of the unit-radius chart
  that agree on the image of `algebraMap P` are equal. This follows from the
  surjectivity of `algebraMap P`.
