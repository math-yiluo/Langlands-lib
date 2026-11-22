# Finite and archimedean data for cuspidal pair poles

`Langlands.Global.cuspidalPairPoleData` proves the data-existence conjunct of
`Langlands.Global.CuspidalPairPoleStatement` for every pair of actual cuspidal
realizations and every pair of spectral presentations satisfying the finite-component
hypotheses. It applies to all ranks and all number fields with compact adele quotient.
The existence of the data is independent of the split-centre hypotheses.

The proof takes the finite pair L-data from `nonempty_finitePairLChoice`, which uses
JPSS factors for the standard additive character and self-dual Haar measures. At
each infinite place it applies `cuspidalArchimedeanParameterExistence` to each
realization and pairs the resulting real or complex standard-module parameters.

Getz and Hahn define the all-place product in *An Introduction to Automorphic
Representations* (2024), equation (11.23), printed p. 308 (PDF p. 319),
and use it in Theorem 11.7.1, printed p. 309 (PDF p. 320). J. W. Cogdell
defines the normalized finite factors in §3.1, Theorem 3.1, printed p. 213
(PDF p. 216), and the all-place product at the opening of §4, printed p. 218
(PDF p. 221), of *Analytic Theory of L-Functions for GLₙ*, chapter 9 in
J. Bernstein and S. Gelbart (eds.), *An Introduction to the Langlands
Program* (Birkhäuser, 2004). Cogdell's §2.3, printed pp. 208–211, and
§§4.1–4.2, printed pp. 219–222, give the surrounding unfolding and global
analytic arguments.
