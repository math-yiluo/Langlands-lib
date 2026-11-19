# The closed Fourier window of the smooth real standard module

`RealStandardCompactClosedStatement` gives closedness of the smooth
real standard module inside its smooth position principal series.
The topology on the principal series is induced by restriction to
`O(n)` with the supremum norm. The block list has total rank `n`.

For a block position, Fourier index and evaluation point in `O(n)`,
the proof integrates a continuous function along the compact rotation
orbit against the unit-modulus Fourier factor. Linearity of integration
and the bound `2π ‖F‖` make this a continuous linear functional on
`C(O(n), ℂ)`. The modes below the absolute induced-block weight give
an intersection of closed kernels.

The Library's compact Fourier criterion identifies the preimage of
this intersection under compact restriction with the actual smooth
standard module. The preimage is closed. Compact restriction is
injective on the smooth principal series by Iwasawa decomposition
and the defining equivariance.

This is an internal topological property of the Library model used
in the principal-series reduction. The closed subset is taken
relative to the smooth position principal series. It supplies the
closed inclusion for studying extension of Whittaker forms in the
smooth topology, where compact restriction is continuous.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 2.4 and §11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
[Casselman, Hecht, and Miličić, *Bruhat filtrations and Whittaker vectors for real groups*, §8](https://www.math.utah.edu/~milicic/Eprints/whittaker.pdf)
