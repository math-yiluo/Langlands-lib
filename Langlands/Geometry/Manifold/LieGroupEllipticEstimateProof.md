# Proof of the interior estimate for elliptic left-invariant word operators

`lieGroupEllipticInteriorEstimate` proves `LieGroupEllipticInteriorEstimateStatement.{u, v}` from
`Langlands.Geometry.Manifold.LieGroupEllipticEstimateStatement`, with no added hypotheses.

## Setting

- `H` is a Lie group modelled on a finite-dimensional real normed space `E`, and
  `X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H`.
- `Ptop` has only words of length `r`, `Plow` has only shorter words, and the word symbol
  `lieWordSymbol X ξ Ptop` is nonzero for every nonzero real linear form `ξ`.

For every word combination `Q`, the theorem gives a compact `V ⊆ H` and `C ≥ 0` such that every
smooth `φ` with `lieWordAction X (Ptop + Plow) φ = 0` satisfies
`‖lieWordAction X Q φ 1‖ ≤ C * M` whenever `‖φ‖ ≤ M` on `V`. This is the interior estimate of
Morrey–Nirenberg (1957), Theorem C, read in a chart at the identity, in pointwise form.

## Proof

1. **Chart.** `exists_lieGroupChartFrame X` (module `LieGroupEllipticChart`) gives an open
   `S ⊆ F = EuclideanSpace ℝ (Fin d)` with `d = finrank ℝ E`, a smooth `ψ` with `ψ x₀ = 1`, and
   smooth vector fields `V i` on `S` with `V i x₀ = toEuclidean (X i)`.
2. **Coordinate operator.** Write `P = Ptop + Plow`; every word in its support has length
   `≤ r`. Let `D` be the `CoordinateScalarOperator` of order `r` with the standard basis and
   coefficients
   `D.coefficient k W x = ∑_{w ∈ supp P} P.coeff w * vectorFieldWordCoeff V w.toList k W x`.
   - These coefficients are `C^∞` on `S` (`contDiffOn_vectorFieldWordCoeff`).
   - By `lieWordDerivative_chart_expansion` with `N = r` and a reordering of finite sums,
     `D.action (φ ∘ ψ) x = lieWordAction X P φ (ψ x)` for `x ∈ S` and smooth `φ`. So `φ ∘ ψ`
     solves `D (φ ∘ ψ) = 0` on `S` whenever `φ` solves the group equation.
3. **Principal symbol.** For a real covector `ξ` on `F`, let `ξ'` be the linear form
   `ξ ∘ toEuclidean` on the tangent space at `1`. Then
   `D.principalSymbol x₀ ξ = lieWordSymbol X ξ' Ptop`.
   - Expand the principal symbol as `∑_{w ∈ supp P} P.coeff w * T w`, where `T w` is the top-order
     pairing of the coefficients of `w`.
   - If `w` has length `r`, then `Plow.coeff w = 0`, and `vectorFieldWordCoeff_symbol` gives
     `T w = ∏_{a ∈ w} ξ (V a x₀) = ∏_{a ∈ w} ξ' (X a)`.
   - If `w` is shorter, then `T w = 0` (`vectorFieldWordCoeff_eq_zero`) and `Ptop.coeff w = 0`.
   - Comparing over `supp P ∪ supp Ptop` with `MonoidAlgebra.lift_apply` and
     `FreeMonoid.lift_apply` gives the word symbol. Since `toEuclidean` is bijective, `ξ ≠ 0`
     forces `ξ' ≠ 0`, so `D` is elliptic at `x₀`.
4. **Euclidean estimate.** `exists_localElliptic_interior_derivative_bounds` (module
   `LocalEllipticInteriorBounds`, any order `r`) gives `R > 0` with `closedBall x₀ R ⊆ S` and
   constants `C_k ≥ 0`. For each solution, `‖iteratedFDeriv ℝ k (φ ∘ ψ) x₀‖ ≤ C_k * M` whenever
   `‖φ ∘ ψ‖ ≤ M` on the ball.
5. **Compact set and constant.** Take `V = ψ '' closedBall x₀ R`. It is compact because the
   closed ball is compact and `ψ` is continuous on `S`. Take
   `C = ∑_{w ∈ supp Q} ‖Q.coeff w‖ * ∑_{k ≤ w.length} ∑_W ‖vectorFieldWordCoeff V w.toList k W x₀‖ * C_k`.
   Neither depends on `φ`.
6. **Bound.** Since `1 = ψ x₀`, expand `lieWordAction X Q φ 1` over `supp Q`, and each word
   derivative by `lieWordDerivative_chart_expansion` with `N = w.length`. The triangle
   inequality, `‖T (e ∘ W)‖ ≤ ‖T‖` for the unit basis vectors, and the bounds of step 4 give
   `‖lieWordAction X Q φ 1‖ ≤ C * M`.

## Supporting modules

The proof uses three new helper modules, each with its own Markdown:
- `Langlands.Analysis.LocalEllipticInteriorBounds`: the Euclidean interior derivative bounds;
- `Langlands.Analysis.VectorFieldWordCoefficients`: coordinate coefficients of words in vector
  fields;
- `Langlands.Geometry.Manifold.LieGroupEllipticChart`: the chart frame at the identity.
