# Totally complex cuspidal spectral rigidity from completed pole profiles

`cuspidalSpectralRigidityTCPoleProfileReduction` gives all three clauses of
`CuspidalSpectralRigidityTCStatement` from a certified completed pair
L-function and its simple pole profile for each pair of split-centre-trivial
cuspidal realizations with irreducible admissible finite components over
each totally complex field. It retains the independent field and
presentation-carrier universes. The pole profiles give holomorphy off
`0` and `1` and a simple pole at each of those points precisely for
contragredient pairs with equal ranks.

The proof derives absolute convergence from the published self-pair
continuation. It obtains partial continuations by cancelling the
archimedean and omitted finite factors in the completed product. The
Landau argument uses the resulting bounds on the partial orders and
positivity of squared power traces to get the exact orders and then the
logarithmic limits. The existing independence and recovery theorems
recover the full multiset of cuspidal constituents from cofinite equality
of the Euler polynomials. This is the recovery premise of the prime cyclic
isobaric base-change assembly.

`cuspidalSpectralRigidityTC_of_normalizedContinuation` uses the published
complex-place parameter theorem and standard finite pair L-data. It applies
the normalized continuation at the standard adelic character. The
archimedean product is the complex-place product because all real-place
parameter types are empty. The resulting completed L-function and its pole
profile are the witnesses for the reduction.

This dependency of the formal argument comes from the partial-continuation
and Landau proofs in `CuspidalPairPartialContinuation` and
`CuspidalSpectralRigidityLandauReduction`. The analytic and recovery steps
there formalize the argument of Jacquet–Shalika (1981), *On Euler Products
and the Classification of Automorphic Representations II*, Theorems 4.1–4.2,
printed pp. 805–807 (PDF pp. 30–32), and the numerical comparison in the
proof of Theorem 4.4, printed p. 809 (PDF p. 34). Registered source
`jacquet-shalika-1981-euler-ii`, SHA-256
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
The completed pole profile uses the normalization of Getz–Hahn (2024),
equation (11.23) and Theorem 11.7.1, printed pp. 308–309 (PDF pp. 319–320).
Registered source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
