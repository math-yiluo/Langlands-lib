# Cuspidal spectral rigidity from completed pair poles and absolute convergence

`Langlands.Automorphic.Unramified.cuspidalSpectralRigidityLandauReduction`
proves `CuspidalSpectralRigidityLandauReductionStatement.{uF,uV}`. Given
`CuspidalPairAbsoluteConvergenceStatement`, the first implication derives
`CuspidalSpectralRigidityStatement` from `CuspidalPairPoleStatement`. The
second derives `CuspidalSpectralRigidityTCStatement` from
`CuspidalPairPoleTCStatement`. Both conclusions retain both universes
and all three conjuncts of the published targets.

`partialPairContinuationReduction` constructs partial continuations with
lower bounds on their meromorphic orders. `landauAsymptoticsReduction`
uses the squared power-trace series to obtain the normalized logarithmic
limits for each field. The trace-independence reduction applies these
limits to the coefficient relation. The constituent-recovery lemmas
derive equality of multiplicities from independence and pass from
Euler polynomial equality to power trace equality by reciprocal roots.
The same fieldwise recovery lemmas apply to the totally complex target.

The arithmetic applications follow H. Jacquet and J. A. Shalika,
*On Euler Products and the Classification of Automorphic Representations
II* (1981), Theorems 4.1–4.2, printed pp. 805–807 (PDF pp. 30–32), and
the numerical comparison in the proof of Theorem 4.4, printed p. 809
(PDF p. 34 in `jacquet-shalika-1981-euler-ii`). The reduction takes
the completed pole profile from J. R. Getz and H. Hahn,
*An Introduction to Automorphic Representations*, Theorem 11.7.1,
p. 309 (PDF p. 320 in `getz-hahn-2024-automorphic-representations`).
It uses the four-factor argument recorded in P. Sarnak,
*Nonvanishing of L-functions on Re(s) = 1*, §1, display (5),
IAS manuscript and PDF p. 3 in `sarnak-nonvanishing-line-one`.
