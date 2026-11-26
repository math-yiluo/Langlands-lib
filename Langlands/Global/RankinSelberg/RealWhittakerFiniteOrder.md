# Finite compact difference order of real Whittaker identity evaluation

## Statement

`RealWhittakerFiniteOrderStatement`: for every list `cs` of real character data, with
`ds = cs.map RealBlock.character`, and every linear map `B` with
`IsRealWhittakerIntertwiner r ds a B`, there are an order `J` and a constant `D ≥ 0` such that

`‖B f 1‖ ≤ D R`

for every standard vector `f` and every `R` with `CompactDifferenceBound J f R`
(`RealCompactDifferences`). `realWhittakerFiniteOrder` proves it. No continuity of `B` is
assumed: the bound is an automatic continuity statement for the Whittaker functional
`f ↦ B f 1` on the `O(r+1)`-finite standard module.

## Proof

Take `C ≥ 1` and `P` from `realWhittakerApproximateIdentity` and put `L = 1 + C`,
`q = 1/(2L)`, `J = P + 1`. Let `A_i` be the approximate identity for `ε = q^i`, and define the
residuals `v_0 = f`, `v_{i+1} = v_i - A_i v_i`, i.e. `v_i = T_i f` for the composite
`T_i = (1 - A_{i-1}) ⋯ (1 - A_0)`, which commutes with compact right translations.

* Each step costs at most a factor `L` at the same order
  (`CompactDifferenceBound.residual`), so `v_m` has a bound of order `J` with constant
  `L^m R`.
* From order `j + 1` to order `j`, step `i` costs at most `2 C q^i`
  (`CompactDifferenceBound.residual_succ`). Applying this for the last `J` steps after `m`
  crude steps, `v_{m+J}` has compact value bound at most `L^m (2 C q^m)^J R`.
* The sampling bound gives `‖B (A_i v_i) 1‖ ≤ C · (bound of v_i) · q^(-iP)`. For `i = m + J`
  the `J = P + 1` factors `q^m` absorb `q^(-(m+J)P)` up to a constant, and `L q = 1/2`, so the
  averaged samples are bounded by a constant times `R 2^(-m)`. The first `J` samples are
  bounded by a finite sum `H R` with `H = Σ_{i<J} C L^i q^(-iP)`.
* By linearity `B f 1 = Σ_{i<N} B (A_i v_i) 1 + B v_N 1`. The last term is
  `ℓ (T_N f)` for the functional `ℓ = (evaluation at 1) ∘ B`; by
  `compactEquivariantOrbitBound` it is at most `S` times the compact value bound of `v_N`,
  which tends to zero. Letting `N → ∞` gives `‖B f 1‖ ≤ (H + 2E) R` with constants
  independent of `f`.

This is the real counterpart of the Library's `ComplexWhittakerFiniteOrder`. It is the
analytic input of the extension of `B` to smooth vectors in `RealExactStandardEvaluation`.
