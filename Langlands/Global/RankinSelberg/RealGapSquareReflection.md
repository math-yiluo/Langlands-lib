# Square reflection at a fixed real Whittaker evaluation point

This module is the real counterpart of the Library's `ComplexGapSquareReflection` and
`ComplexGapSquareAverage`. Write `H = GL_{t+1}(ℝ)`, `O = O(t+1)` for the orthogonal group (as
`Matrix.unitaryGroup`, mapped to `H` by `Unitary.toUnits`), `ι` for inverse transpose, and
`realAdjacentMatrixWeight η Φ s y = Φ(y) η(det y) |det y|^{s + t/2}` for the square weight of
`RealLocalAdjacentUnfolding`.

* `matrixWeight_eq_weightedTest`: `realAdjacentMatrixWeight η_c Φ s y` is the Library's weighted square
  test `realWeightedMatrixTest c Φ (s + t/2) y`.
* `integrable_compactInsertion`: for a compact group `K` with a finite measure `ν`, a continuous
  homomorphism `K → H`, a continuous weight `κ`, a square Schwartz test `Ψ` and a continuous `V` with
  `‖V g‖ ≤ C · realMatrixHeight(g)^N`, the function
  `(k, g) ↦ κ(k) · realWeightedMatrixTest d Ψ w (k^{-1} g) · V(x g)` is integrable for `ν × μ` (any Haar
  measure `μ` on `H`) when `t + 1 + 2N ≤ Re d.exponent + Re w`. This is the rank-`t+1` form of the
  Library's `RealGodement.integrable_realCompactInsertion`.

`RealGapSquareReflectionStatement` (proved by `realGapSquareReflection`): let `D` be a real quotient
measure datum of rank `t`, `a ∈ ℝˣ`, `c` a real character datum, `fs` a list of `t + 1` character data
with block list `es`, `Φ` a square Schwartz test whose left translates by `O` span a finite-dimensional
space, `B` a uniform real Whittaker map of character `a` on the compact-finite standard module of `es`,
`f` a vector of that module and `x ∈ H`. Put `Φ̂ = realRectangularSchwartzFourier a Φ`. Then on some right
half-plane the functions `y ↦ realAdjacentMatrixWeight η_c Φ s y · B f (x y)` and
`y ↦ realAdjacentMatrixWeight η_{c⁻¹} Φ̂ s y · B f (x ι(y))` are integrable for `D.groupHaar`, and their
integrals satisfy `HasRealPairNormalizedGrowth` for the lists `[c]` and `es`, their blockwise duals,
the parameter `a`, the scale `√|a|` and the sign `1`.

The proof follows the construction of the Library's `RealAdjacentCanonicalChamber`.
`exists_realCompactMatrixWeight` gives a continuous weight `κ` on `O`, with finite left span, that
reproduces `Φ` with `c`. Since orthogonal determinants are `±1`, `κ` also reproduces `Φ` with `c⁻¹`
(`realCompactMatrixTranslate_inverse_of_mem`), and then `Φ̂` with `c⁻¹` (`realLocalCompactFourierWeight`).
The compact average moves from the test to the coefficient by
`ComplexJacquet.integral_of_compact_average`, using `realWeightedMatrixTest_reproduce` and
`integrable_compactInsertion`. Then `realOrthogonalCompactProjectionPremise` and
`realLocalCompactProjectionReduction` expand the averaged coefficient as a finite sum
`∑_j W_j(x) C_j(y)`, with `C_j(y) = ∫ κ'_j(k) f(k y) dk`. For the dual integral the same expansion is
used at `ι(y)`, since `ι(k y) = k ι(y)` for orthogonal `k`. Each pair of square integrals of `C_j` has the
normalized equation by `realAdjacentSquareGrowth`. Finite sums with the constant coefficients `W_j(x)`
and agreement on a right half-plane (`HasRealPairNormalizedGrowth.sum`, `.const_mul`, `.congr`) give the
conclusion. The finite left orthogonal span of `Φ` is the hypothesis used by this compact-projection
proof. In Jacquet, *Archimedean Rankin–Selberg integrals* (2009), the square step is (10.10) in §10.3,
p. 76, which invokes the matrix functional equation of Proposition 4.4, p. 31.
