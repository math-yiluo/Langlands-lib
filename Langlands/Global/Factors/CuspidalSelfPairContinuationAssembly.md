# Lemma (5.2) of Jacquet–Shalika I from bounds on finite self-pair Euler products

Module `Langlands.Global.Factors.CuspidalSelfPairContinuationAssembly`, namespace
`Langlands.Global.CuspidalSelfPairAssembly`.

This internal helper is the last step of the positivity proof of
`CuspidalSelfPairContinuationStatement` (Jacquet–Shalika 1981, I, Lemma (5.2)).
It contains no `Prop`-valued statement definitions.

Fix the data of that statement:

* a cuspidal realization `T` with unitary central character (`hT`);
* a realization `Td` of its contragredient (`hTd`);
* spectral presentations `P` of `T` and `Pd` of `Td`;
* a finite set `S` of finite places containing both exceptional sets.

The module reduces the conclusion of the statement for these data to one hypothesis. For
every real `σ > 1`, the finite partial products `‖∏_(v ∈ E) L(σ, π_v × π̃_v)‖` must be bounded
uniformly in the finite set `E` of places outside `S`. Here `L(s, π_v × π̃_v)` is
`CuspidalPairBoundaryNonvanishing.partialEulerFactor P Pd hP hPd v s`.

## Imported machinery

The module imports `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`, the
proof of `CuspidalPairAbsoluteConvergenceReductionStatement`. From it, this module uses:

* `selfCoeff P hP (v, n) = |tr A_v ^ (n + 1)|² / (n + 1) ≥ 0` and
  `logExponent (v, n) = (n + 1) log q_v`;
* `logEulerTerm_self_eq`: for the contragredient presentation, the term of the double
  series of `log L^S(s, π × π̃)` is `selfCoeff · exp (-logExponent · s)`. The proof uses
  that the spectrum of `Pd` is the complex conjugate of that of `P`
  (`eigenvalues_eq_conjSpectrum`).
* The local logarithm `exists_hasSum_logEulerTerm` (JS I, (5.3.1)).
* The bounds `|α| ≤ q_v ^ (1/2)` (`norm_eigenvalue_le_sqrt`, JS I, Corollary (2.5)).
* `summable_and_hasProd_of_summable`: the product is the exponential of the double
  series (JS I, (5.3.2)).
* The general Dirichlet series API `Langlands.GeneralDirichlet`.

## Main results

* `bound_P`, `bound_Pd`: the bounds `|α| ≤ q_v ^ (1/2)` outside `S` for `P` and for `Pd`.
  The spectrum of `Pd` is the conjugate of that of `P`.
* `logEulerTerm_eq_term`: the self-pair term equals `GeneralDirichlet.term selfCoeff
  logExponent`.
* `continuation_of_summableAt`: suppose the self-pair series
  `∑_(v ∉ S, n) selfCoeff (v, n) q_v ^ (-(n+1)σ)` converges at every real `σ > 1`. Then
  `L = exp ∘ GeneralDirichlet.series selfCoeff logExponent` has three properties:
  * it is holomorphic on `Re s > 1`;
  * for every `s` with `Re s > 1`, `∑_v ‖L(s, π_v × π̃_v) − 1‖` converges;
  * for every such `s`, the Euler product has `HasProd` with value `L s`.

  The `σ` of the statement is `1`.
* `partialEulerFactor_real`: at a real point `σ > 1`, the local factor is `exp a_v`. Here
  `a_v` is the sum of the nonnegative local series `∑_n selfCoeff (v, n) q_v ^ (-(n+1)σ)`.
* `summableAt_of_prod_bound`: suppose that at a real `σ > 1` all finite partial products
  have norm at most `M`. Then the self-pair double series converges at `σ`.
* **`continuation_of_prod_bound`**: the conclusion of `CuspidalSelfPairContinuationStatement`
  for the fixed data, given such a bound `M(σ)` for every real `σ > 1`.
* `norm_prod_eq_exp`: if every local factor at `σ` is `exp a_v` with `a_v` real, then the
  norm of a finite partial product is `exp (∑_(v ∈ E) a_v)`.
* `prod_bound_of_other`: let `S₁` be another finite set containing both exceptional sets.
  In the application `S₁ = S ∪ (ramification of ψ)`, needed because the Library's
  one-place Euler step requires `ψ` to be unramified outside the set. Suppose the finite
  partial products over places outside `S₁` are bounded at `σ`. Then so are those over
  places outside `S`, with bound `M · exp (∑_(v ∈ S₁ \ S) a_v)`.
* **`continuation_of_prod_bound_other`**: the conclusion of
  `CuspidalSelfPairContinuationStatement` for the data `T, Td, P, Pd, S`, given bounds on the
  finite partial products outside such an `S₁` at every real `σ > 1`.

## Proof outline

**From convergence to the statement.** Let `Re s > 1`. The self-pair term at `s` has norm
`selfCoeff · exp (-logExponent · Re s)`, so convergence at the real point `Re s` gives
absolute convergence of the double series at `s`.
`summable_and_hasProd_of_summable` then gives absolute convergence of the Euler product
and `HasProd` with value `exp (∑ logEulerTerm)`. That sum is
`GeneralDirichlet.series selfCoeff logExponent s`. Holomorphy of the series on `Re s > 1` is
`GeneralDirichlet.differentiableOn_series`, which applies because the coefficients are
nonnegative and the series converges at every real `σ > 1`. Holomorphy of `L` follows by
composing with `exp`.

**From bounded products to convergence.** At a real `σ > 1`, the local logarithm
`exists_hasSum_logEulerTerm` and `logEulerTerm_self_eq` show that the series of the local
logarithm has real nonnegative terms. Their sum is a real number `a_v ≥ 0` with
`L(σ, π_v × π̃_v) = exp a_v`. Hence `‖∏_(v ∈ E) L(σ, π_v × π̃_v)‖ = exp (∑_(v ∈ E) a_v)`. The
bound by `M` gives `∑_(v ∈ E) a_v ≤ log M` for every finite `E` (`M > 0` from `E = ∅`).
So `a` is summable (`summable_of_sum_le`). The nonnegative double family is then summable
by `summable_prod_of_nonneg`: each fiber has sum `a_v`, and `a` is summable.

**Changing `S`.** Split a finite set `E` of places outside `S` into the places outside `S₁`
and the rest. The first part maps injectively to a finite set of places outside `S₁`, with
the same local factors (`partialEulerFactor` depends on the place only). Its product is
therefore bounded by `M`. The rest lies in the finite set `K` of places of `S₁` outside
`S`. Its product has norm `exp (∑ a_v) ≤ exp (∑_(v ∈ K) a_v)`, since `a_v ≥ 0`.

## Route and provenance

This is the end of the proof of Lemma (5.2) along the positivity route. JS I prove
Lemma (5.2) on p. 555 by dividing the global integral by local integrals chosen nonzero at a
given point. The positivity route avoids that local nonvanishing. It bounds the finite
partial products at real points by `Ψ(σ)/Ψ_S(σ)`, ratios of nonnegative partial global
Whittaker integrals of `|W|² Φ |det|^σ`. This mirrors the positivity used in the proof of
(4.8), p. 553. The bound itself is supplied separately. The passage from convergence of the
nonnegative double series to the Euler product follows JS I, (5.3.1)–(5.3.2), through the
imported machinery of `CuspidalPairAbsoluteConvergenceProof`.
