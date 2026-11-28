# Plancherel in one factor of a product measure

`coordinatePartialFourier` takes the positive-phase Fourier integral in
the `Fin m → ℝ` coordinate of a complex-valued function on a product.
`CoordinatePartialPlancherelStatement` assumes an s-finite measure `μ`
(a countable sum of finite measures) on the second factor `Q`. Both
functions are jointly square integrable for `volume.prod μ`, where
`volume` is unscaled Lebesgue measure on `Fin m → ℝ`. For `μ`-almost
every point of `Q`, each frequency slice is Lebesgue integrable. The
transforms are jointly square integrable for `volume.prod μ`, with
unscaled Lebesgue measure also in the Fourier variable. Their pairing is
`(2π)^m` times the original product-measure pairing. Both pairings
conjugate the second function.

The proof first replaces each function by a strongly measurable
representative to obtain joint almost-everywhere strong measurability
after transformation. Fubini gives agreement of the representatives
on almost every frequency slice, which gives agreement of the Fourier
integrals at each Fourier variable on those slices. Applying scalar
Plancherel to the diagonal pairing gives the squared-norm identity on
each such slice. This yields joint square integrability by Fubini.
Hölder's inequality gives integrable products on both sides, so Fubini
and scalar Plancherel give the pairing identity.

This is the product-measure Plancherel step for the split-centre Fourier
transform in E. Lapid, *On Arthur's asymptotic inner product formula of
truncated Eisenstein series* (2011), §8, printed p.328 (volume PDF p.337).
The second factor in that application is the norm-one adelic quotient.
