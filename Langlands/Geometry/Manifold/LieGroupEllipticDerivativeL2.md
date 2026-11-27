# Local Haar `L²` control of word derivatives for an elliptic word equation

Module `Langlands.Geometry.Manifold.LieGroupEllipticDerivativeL2`, namespace
`Langlands.Geometry.Manifold`.

| Declaration | Kind |
| --- | --- |
| `lieWordDerivative_ofList_eq_foldr` | theorem |
| `foldr_groupDirectionalValue_eq_lieWordDerivative` | theorem |
| `exists_lieWord_derivative_l2_evaluation` | theorem |

## Words and iterated directional derivatives

`lieWordDerivative_ofList_eq_foldr Y w φ`: for tangent directions `Y : Fin m → 𝔤` and a list
of indices `w`, the word derivative `lieWordDerivative Y (FreeMonoid.ofList w) φ` is the
right fold of `groupDirectionalValue` along the list of directions `w.map Y`, that is
`D_{Y w₀} (D_{Y w₁} (⋯ φ))`. The proof is an induction on `w` with
`lieWordDerivative_ofList_nil` and `lieWordDerivative_ofList_cons`.

`foldr_groupDirectionalValue_eq_lieWordDerivative D φ`: every list `D` of tangent directions is
the word `List.finRange D.length` in the directions `i ↦ D.get i`; this is the previous lemma
with `List.map_get_finRange`.

## The estimate

`exists_lieWord_derivative_l2_evaluation`: let `H` be a Lie group modelled on a
finite-dimensional real normed space, second countable and Hausdorff, with a Haar measure `μ`.
Let `X i` be finitely many tangent vectors at the identity, `Ptop` a combination of words of one
length `r > 0` whose symbol `lieWordSymbol X ξ Ptop` vanishes at no nonzero real covector `ξ`,
and `Plow` a combination of shorter words. For arbitrary tangent directions `Y : Fin m → 𝔤` and
every list of indices `w` there are a compact `V ⊆ H` and a constant `C < ∞` such that every
smooth `φ : H → ℂ` with `lieWordAction X (Ptop + Plow) φ = 0` satisfies

`‖(lieWordDerivative Y (FreeMonoid.ofList w) φ) 1‖ₑ ≤ C · ‖φ‖_{L²(μ|_V)}`.

The case of the empty word is the Library theorem `exists_lieWord_l2_evaluation`.

*Proof.* Work in the Euclidean identity chart `ψ = (extChartAt 1)⁻¹ ∘ toEuclidean⁻¹` on
`S = toEuclidean⁻¹' (extChartAt 1).target`, with chart point `x₀` (`ψ x₀ = 1`).

1. `exists_lieWordCoordinateOperator` turns the elliptic word operator into a scalar coordinate
   operator `D` on `S` with smooth coefficients, elliptic at `x₀`, with
   `D (φ ∘ ψ) = (lieWordAction X (Ptop + Plow) φ) ∘ ψ` on `S`.
2. `exists_lieGroupChartFrame_extChart Y` gives smooth vector fields `V'` on the same `S` for the
   same `ψ` and `x₀`; `lieWordDerivative_chart_expansion` then writes the `w`-derivative of `φ` at
   `ψ x₀ = 1` as `∑_{k ≤ |w|} ∑_W c_{k,W}(x₀) · D^k(φ ∘ ψ)(x₀)(e_{W 0}, …, e_{W (k-1)})`, with the
   coefficients `c_{k,W} = vectorFieldWordCoeff V' w k W` and the standard orthonormal basis `e`.
3. `exists_chartVolume_le_smul_haar` gives a closed ball `B(x₀, R) ⊆ S` on which the chart image
   of Lebesgue measure is at most `c · μ`. `exists_localElliptic_interior_derivative_l2_bounds`,
   applied to `D` on the open ball `B(x₀, R)`, gives `ρ` and constants `C_k` with
   `‖D^k u(x₀)‖ₑ ≤ C_k ‖u‖_{L²(B̄(x₀, ρ))}` for every smooth solution `u` of `D u = 0` and every
   order `k`; it applies to `u = φ ∘ ψ`.
4. Each term of the expansion is at most `‖c_{k,W}(x₀)‖ₑ C_k ‖φ ∘ ψ‖_{L²(B̄(x₀, ρ))}`, because a
   continuous multilinear map evaluated on unit vectors is bounded by its norm. With
   `V = ψ(B̄(x₀, R))` (compact), the `L²` norm of `φ ∘ ψ` on the small ball is at most the norm of
   `φ` for the image measure, which is at most `c^{1/2} ‖φ‖_{L²(μ|_V)}`
   (`eLpNorm_map_measure`, `eLpNorm_le_of_measure_le_smul`). So the statement holds with
   `C = (∑_{k ≤ |w|} ∑_W ‖c_{k,W}(x₀)‖ₑ C_k) · c^{1/2}`.

The constant depends on the operator, the directions `Y` and the word `w`, not on `φ`. The proof
is an internal composition of the Library's chart, coordinate-expansion and interior-estimate
theorems; it follows the proof of `exists_lieWord_l2_evaluation` with derivatives of all orders up
to `|w|` in place of the value.
