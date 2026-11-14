# Differentiating Whittaker coefficients along right-translation curves

Module `Langlands.Automorphic.CuspidalWhittaker.CurveDerivative`, namespace
`Langlands.Automorphic.CuspidalWhittaker`. Worker 174 wrote it for the proof of
`Langlands.Automorphic.CuspidalArchimedeanWhittakerFunctionalStatement` (Task 5996,
`e3f48d66-76bc-4321-a8ea-e25681c89d3f`, published under Task 5720).

Throughout, `K` is a number field with compact adele quotient `𝔸_K / K`. The Library's
Whittaker iteration (module `CuspidalWhittaker.WhittakerCoefficient`) builds, from a function
`F` on `GL_{r+1}(𝔸_K)`, the column coefficients `colCoeff c F` (Fourier coefficients over the
compact torus `(𝔸_K / K)^{r+1}` in one column) and the iterated Whittaker coefficient
`descend k F` (`k` column coefficients in turn). `LevelProps k F` collects the continuity,
invariance, vanishing and equivariance hypotheses under which the iteration is well behaved.

## Definition

`HasCurveDeriv e F G`, for a curve `e : ℝ → GL_{r+1}(𝔸_K)` and functions `F, G`, says that for
every `g` and every `t`, `s ↦ F(g · e(s))` has derivative `G(g · e(t))` at `t`. Provenance:
internal; it is the derivative of `F` along right translation by `e`, the form in which the
Lie action of a cuspidal realization differentiates realized forms along one-parameter
subgroups.

## Results

- `hasDerivAt_torusIntegral`: let `Φ s` and `Ψ s` be periodic functions on `𝔸_K^ι` (for a
  finite type `ι`), with `Φ s` continuous for every `s`, `Ψ` jointly continuous in `(s, y)`
  and `∂ₛ Φ s y = Ψ s y` at every `s`. Then `s ↦ ∫_{torus} Φ s` has derivative
  `∫_{torus} Ψ t` at `t`. Proof: the integrals are over the compact torus
  `(𝔸_K / K)^ι` with its Haar measure, through `torusLift`. `Ψ` descends to a continuous
  function on `ℝ × (𝔸_K / K)^ι` (the product of `id` and the quotient map is an open quotient
  map). It is therefore bounded by a constant `C` on the compact set
  `closedBall t 1 × torus`. Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  then applies with the constant bound `C`, which is integrable on the compact torus.
- `HasCurveDeriv.colCoeff`: if `e` is continuous, `F` and `G` satisfy `LevelProps (c + 1)`
  and `HasCurveDeriv e F G`, then `HasCurveDeriv e (colCoeff c F) (colCoeff c G)`. If
  `c < r`, the column coefficient at `g · e(s)` is the torus integral of
  `y ↦ F(u(y) · g · e(s)) · conj ψ(y)`, with `u(y)` the column unipotent element. The
  previous lemma applies with these integrands, whose periodicity and continuity come from
  the level properties. Differentiation of the integrand is the hypothesis at the point
  `u(y) · g`, multiplied by the constant `conj ψ(y)`. If `c ≥ r` the column coefficient is
  `F` itself.
- `HasCurveDeriv.descend`: for `k ≤ r`, if `F` and `G` satisfy `LevelProps k` and
  `HasCurveDeriv e F G`, then `HasCurveDeriv e (descend k F) (descend k G)`. Induction on
  `k`, using `LevelProps.colCoeff` to keep the level properties at each step.
