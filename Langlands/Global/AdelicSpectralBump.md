# A common smooth compact coefficient for ambient spectral profiles

`Langlands.Global.spectralBump m` is a specific coefficient on the real
coordinate space `Fin m → ℝ`. It takes the real smooth bump centered at zero,
with inner and outer radii `1` and `2` in the coordinate norm, and regards its
values as complex. The subtype carries smoothness, compact support and the value
`1` at the origin. The last property ensures that the coefficient is not the
zero function. The construction also applies at `m = 0`.

This is an internal choice for the ambient-factor comparison of wave packets.
Once one chart for the ambient parameter space is fixed, the same coefficient
can be used with any parabolic, since it depends only on the dimension of that
chart. No normalization of the integral of the coefficient is stipulated. The
construction itself does not assert any norm or positivity property of its
Fourier profile.
