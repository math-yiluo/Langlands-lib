# Proof: partial Euler factorization of the equal-rank global Whittaker integral

The theorem `Langlands.Global.RankinSelbergGlobal.equalEulerFactorization` proves the Library
statement `Langlands.Global.RankinSelbergGlobal.EqualEulerFactorizationStatement.{u, uQ}`
(module `Langlands.Global.RankinSelberg.EqualEulerFactorizationStatement`). The universe
parameters are `u` (the number field) and `uQ` (the local factors of the spectral
presentations). The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

The statement Markdown cites Cogdell 2004, §2.3 (printed p.210), with Theorem 3.3 (p.215).
Cogdell unfolds the global integral to an integral over `N_n(𝔸)\GL_n(𝔸)` and says it
"converges for Re(s) ≫ 0", without a proof. He then factors it by the unramified
computation at the places outside `S`. The Lean proof has the same two parts. The
convergence comes from the Library's uniform Whittaker–Schwartz estimate. The factorization
is done one place at a time.

## The proof

The proof is one line:

```lean
theorem equalEulerFactorization : EqualEulerFactorizationStatement.{u, uQ} :=
  equalEulerFactorization_of_whittakerSchwartzGauge whittakerSchwartzGauge
```

Both ingredients are published Library theorems.

- `whittakerSchwartzGauge : WhittakerSchwartzGaugeStatement.{u}` (module
  `Langlands.Global.RankinSelberg.WhittakerSchwartzGauge`) is the analytic input. Let `F` be
  a number field with compact `F\𝔸`, and let `V` be a space of functions on
  `GL_(r+1)(𝔸)` that is an analytic Whittaker decay class (`WhittakerDecayClass`) and whose
  functions share one central power exponent (`HasCentralPowerBound`). Then the weighted
  Whittaker–Schwartz integral
  `∫ ‖W_f(g)‖ ‖Φ(e_(r+1) g)‖ |det g|^σ` over `N(𝔸)\GL_(r+1)(𝔸)` is finite for `σ` above a
  threshold. The threshold is uniform over standard characters, functions `f ∈ V` and
  Schwartz–Bruhat functions `Φ` (`WhittakerSchwartzBound`).
- `equalEulerFactorization_of_whittakerSchwartzGauge` (module
  `Langlands.Global.RankinSelberg.EqualEulerGaugeReduction`) derives
  `EqualEulerFactorizationStatement` from `WhittakerSchwartzGaugeStatement`.

## What the reduction does

`equalEulerFactorization_of_whittakerSchwartzGauge h` is
`equalEulerGaugeReduction (equalGaugeSpecialization h)`. The steps are:

1. `equalGaugeSpecialization` (module `EqualGaugeSpecialization`) applies the general
   estimate to the cusp space of each cuspidal realization `T` (with its archimedean
   derivative action): it gives `EqualWhittakerSchwartzStatement`.
2. `equalGaugeReduction` turns this into the primal gauge premise
   `EqualWhittakerGaugeIntegrable F T T'` for every equal-rank pair.
3. `equalEulerFactorization_of_gauge` proves the target from that premise:
   - `integrable_equalWhittakerIntegrand_of_gauge` gives a constant `C₀` above which the
     equal-rank Whittaker integrand is integrable for the quotient measure. This is the
     absolute convergence part of the conclusion.
   - `exists_partialEulerFactor_convergence` gives `σ₂` above which the unramified pair
     factors `partialEulerFactor P P' hP hP' v s` are summable around 1 and have a product
     `p` (`partialEulerProduct`).
   - `exists_hasSatakeBound_presentation` bounds the Satake parameters of `P` and `P'` by
     constants `C`, `C'`. These give the radius `EqualEulerLocal.localRadius r C C'`
     above which each local sum converges.
   - The chosen half-plane is `Re s > max C₀ (max σ₂ (localRadius r C C'))`.
   - At each finite place `v ∉ S`, `EqualEulerReduction.setIntegral_insert` factors out the
     local term. It uses the spherical factorization (A)
     `UnramifiedWhittaker.unramifiedWhittakerFactorization`, the cell decomposition
     `whittakerCellDecomposition`, and the local sum of module `EqualEulerLocalSum`.
     Moving `v` from the "outside `S`" part to the partial integral multiplies by the local
     factor `L(s, Π_v × Π'_v)`.
   - `integral_eq_hasProd_mul_setIntegral` passes to the limit over finite sets of places
     and gives `equalWhittakerIntegral = partialEqualWhittakerIntegral · p`.

## Provenance

This is an internal proof assembled from published Library results. The analytic estimate
fills the convergence step that Cogdell states without proof. The factorization follows
Cogdell's unramified computation (Shintani's formula, via the Library's (A)), done one
place at a time.
