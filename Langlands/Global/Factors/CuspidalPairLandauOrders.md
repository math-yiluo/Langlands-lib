# Exact boundary orders from positivity of squared traces

`Langlands.Global.CuspidalPairLandauOrders.landauAsymptoticsReduction` proves
`LandauAsymptoticsReductionStatement.{u,uQ}`. Given absolute convergence
of the cuspidal pair logarithmic series and `PartialPairContinuationAt F`,
it proves `CuspidalPairLogAsymptoticsAt F` over that field. The proof uses
the exponential identity, the meromorphic continuation, analyticity off
`0` and `1`, and the lower bounds on the meromorphic order at `1`.

## Local coefficients

The local identities express the two self-pair logarithmic terms and the
two conjugate shifted cross-pair terms as one term of a squared power-trace
series. The test spectrum is the direct sum of the first spectrum and
the conjugate of the second multiplied by the phase
`exp(i θ log qᵥ)`. Complex conjugation relates the cross-pair terms at
conjugate arguments. The self-pair series uses one spectrum.

A spectrum of positive rank whose inverse and conjugate multisets agree
has an eigenvalue of norm at least one. Indeed, if an eigenvalue has
norm below one, an eigenvalue conjugate to its inverse has norm above
one. For the cuspidal presentations this multiset equality follows from
the comparisons with a presentation of the actual conjugate realization.
The direct sum retains the first spectrum's large eigenvalue.

## Exact orders

At zero shift in the contragredient case, the logarithmic series is the
series of squared power traces of the second spectrum. The positive real
pole detection criterion applied to the partial continuation forces a
pole at `1`. The lower bound on its order makes it simple.

In the other cases, choose spectral presentations of the two conjugate
realizations and enlarge the omitted set to contain their exceptional
places. Absolute convergence lets the four series be added termwise
on the right half-plane. The local square identity then expresses the
product of the four continuations as the exponential of a nonnegative
series. The cross-factors with opposite imaginary shifts have equal
norms on the right real ray. `SpectralSquare.crossOrder_eq_zero` gives
order zero of the first cross-factor at the shifted boundary point.

Enlarging the omitted set multiplies the partial function by the entire
product of the additional Euler denominators. The proof splits the Euler
product on a sufficiently far right half-plane and then uses the
meromorphic identity theorem to identify orders. Thus the order for
the original set is at most the order for the enlarged set. The original
order is nonnegative by the continuation bounds, so it equals zero.

Finally, `LogarithmicAsymptotics.tendsto_div_log_of_meromorphicOrderAt`
applies to the logarithmic series itself as a continuous logarithm
along the right horizontal ray. Its limit after normalization is the
negative of the exact order, which gives both clauses of the fieldwise
logarithmic asymptotic.

## Provenance

- H. Jacquet and J. A. Shalika, *On Euler Products and the Classification
  of Automorphic Representations II* (1981), Theorem 4.1 and its proof,
  printed pp. 805–806 (PDF pp. 30–31 in `jacquet-shalika-1981-euler-ii`),
  give the boundary limit used for independence.
- P. Sarnak, *Nonvanishing of L-functions on Re(s) = 1*, §1, display (5),
  IAS manuscript and PDF p. 3 (`sarnak-nonvanishing-line-one`), records
  the four-factor positivity argument. The Lean proof applies the
  criterion proved in `SpectralSquarePoles` to the partial factors and
  uses the finite deletion comparison for arbitrary omitted sets.
- The real pole criterion uses the meromorphic form of Hardy and Riesz,
  *The General Theory of Dirichlet's Series*, Theorem 10, printed p. 10
  (PDF p. 26 in `hardy-riesz-1915-dirichlet-series`).
