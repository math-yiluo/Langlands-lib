# Proof: the chart algebras of the affine analytification are flat

Author: Worker 387 (Task 7655, in agreement with its first executor Worker 930).

`Langlands.Analytic.AffineAnalytification.affineAnalytificationChartFlat` proves
the published statement
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationChartFlatStatement.{u, v}`
in all universes, with no added hypothesis. Let `K : Type u` be a complete,
ultrametric, nontrivially normed field. Let `A : Type v` be a commutative
`K`-algebra with a finite polynomial presentation `P`, and let `m : ℕ`. Then
`(PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity m)).toRingHom`
is flat (`RingHom.Flat`). The theorem applies
`ChartFlatness.flat_chartAlgebraMap K P m`.

The statement, its source and its hypotheses are documented in
`AffineAnalytificationChartFlatStatement.md`. Task 7657 is the focused proof
task for that statement. This proof was written inside Task 7655, whose proof of
`AffineAnalytificationFiniteGermComparisonStatement` uses it.

## Provenance and route

The route follows the outline in the statement's Markdown. It is the
argument of Berkovich 1990, proof of Theorem 3.4.1 (printed pp.63–64, PDF
pp.77–78), specialized to the Library's polydisc charts. Flatness of
`K[T] → K{r⁻¹T}` comes from agreement of completions at maximal ideals (rigid
points). Flatness of the chart algebra over `A` follows by base change. The
helper modules supply the parts:

- `TruncatedComparisonFlatness`: flatness of a localization at a maximal ideal
  from bijective truncated comparison maps, through adic completions.
- `TatePolynomialFlatness`: flatness of `polynomialMap n : K[T₁, …, Tₙ] →
  K⟨T₁, …, Tₙ⟩` for the radius-one Tate algebra.

This module transfers that flatness to the chart radius and passes to the
quotient by the presentation kernel. Its auxiliary declarations live in the
namespace `Langlands.Analytic.ChartFlatness`.

## Declarations

Write `n = P.arity`, `r = polyradius K n m` (every component equal to
`radius K m = ‖scale K‖⁻¹ ^ m`), and `GTA r = GeneralizedTateAlgebra r K`.

- `flat_quotientMap f hf I`: if `f : R → S` is flat, then so is the induced
  map `R ⧸ I → S ⧸ I S`. Mathlib's
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` identifies `S ⧸ I S` with
  the base change `R ⧸ I ⊗[R] S`, which is flat over `R ⧸ I`.
- `chartScalar K m = (scale K)⁻¹ ^ m`. It is nonzero (`chartScalar_ne_zero`),
  and its norm is the radius `r i` (`norm_chartScalar`).
- `chartRescale K n m : GTA r →+* K⟨T₁, …, Tₙ⟩` is the Library's
  `GeneralizedTateAlgebra.baseChange` (module
  `GeneralizedAffinoid.StrictBaseChange`) with the identity of `K` and
  rescaling constants `c i = chartScalar K m`. It sends `∑ a_d T^d` to
  `∑ c^d a_d T^d` (`coeff_chartRescale`). It preserves norms
  (`norm_chartRescale`), so it is injective. It is surjective because the
  Library's `GeneralizedTateAlgebra.descend` with the identity of `K` gives a
  preimage, and the scalings `c^d` and `c^{-d}` cancel. Together these give
  `chartRescale_bijective`.
- `chartRescale_monomial`, `strictMonomial_zero`, `strictMonomial_eq_mul`:
  computations of `chartRescale` and of strict monomials on monomials.
- `polyRescale K n a`: the `K`-algebra endomorphism `Tᵢ ↦ a Tᵢ` of
  `K[T₁, …, Tₙ]`. `polyRescale_comp` and `polyRescale_one` give
  `polyRescale a ∘ polyRescale b = polyRescale (a b)` and
  `polyRescale 1 = id`, so `polyRescale a` is bijective for `a ≠ 0`
  (`polyRescale_bijective`).
- `chartRescale_comp_polynomialMap`:
  `chartRescale ∘ GeneralizedTateAlgebra.polynomialMap r K =
  TatePolynomialFlatness.polynomialMap n ∘ polyRescale (chartScalar K m)`. It is
  checked on constants and on the variables `Tᵢ`. Both sides send `Tᵢ` to
  `c Tᵢ`.
- `flat_chartPolynomialMap`: `GeneralizedTateAlgebra.polynomialMap r K :
  K[T₁, …, Tₙ] → GTA r` is flat. The right-hand side above is flat, by
  `polyRescale_bijective` and `TatePolynomialFlatness.flat_polynomialMap`. The
  bijective `chartRescale` on the left can be removed
  (`RingHom.Flat.comp_iff_of_bijective_left`).
- `isClosed_ideal`: every ideal `J` of `GTA r` is closed. `chartRescale` is an
  isometric ring bijection, so `J` is the preimage of its image. The image is
  an ideal of the Noetherian Banach algebra `K⟨T₁, …, Tₙ⟩`, hence closed
  (`isClosed_ideal_of_noetherian_banach`). Preimages of closed sets under the
  continuous `chartRescale` are closed.
- `chart_ideal_eq`: the ideal of the chart
  `PolynomialLocus.chart P r` is the extension `I · GTA r` of
  `I = RingHom.ker P.map`. By definition it is the closure of the ideal
  spanned by the image of `I` under `polynomialMap r K`. This ideal is closed
  by `isClosed_ideal`, and it equals `I.map (polynomialMap r K)`.
- `flat_chartAlgebraMap`: the main step. See below.

## Proof of `flat_chartAlgebraMap`

Let `ψ = GeneralizedTateAlgebra.polynomialMap r K` and `I = ker P.map`.

1. `P.map` is surjective, so `e : K[T] ⧸ I ≃+* A`
   (`RingHom.quotientKerEquivOfSurjective`).
2. The ideal `J` of the chart algebra equals `I.map ψ` (`chart_ideal_eq`). So
   `q : GTA r ⧸ J ≃+* GTA r ⧸ I.map ψ` (`Ideal.quotEquivOfEq`).
3. The composite `q ∘ PolynomialLocus.algebraMap P r ∘ e` is the induced
   quotient map `K[T] ⧸ I → GTA r ⧸ I.map ψ`. Both send the class of `p` to the
   class of `ψ p`, by `PolynomialLocus.algebraMap_map`.
4. That quotient map is flat by `flat_quotientMap` applied to
   `flat_chartPolynomialMap`.
5. Composing with the ring isomorphisms `e` and `q` preserves and reflects
   flatness (`RingHom.Flat.comp_iff_of_bijective_right` and `_left`). So
   `PolynomialLocus.algebraMap P r` is flat.

## Scope and dependencies

The proof uses no hypothesis beyond those of the statement. `A` may be the
zero algebra, and `n = 0` is allowed. It does not use
`AffineAnalytificationEtaleStatement` or any statement whose proof is meant to
use this one. Besides Mathlib, it uses the published Library modules
`AffineAnalytificationChartFlatStatement`, `PolynomialLocusCharts`,
`GeneralizedAffinoid.StrictBaseChange`, `ClosedIdealsBanach`,
`TateNoetherian`, `TateRegrouping`, `TateShearPolynomial`,
`DistinguishedNormalization`, `WeierstrassQuotient`, `NoetherNormalization`
and `FlatTargetDescent`, and the two new helper modules named above. The
axioms are `propext`, `Classical.choice` and `Quot.sound`.
