# Iterated Fourier coefficients on the real compact model

`RealCompactIteratedFourierStatement` says that the iterated Fourier
coefficients for every list of modes determine the compact restriction
of a continuous compact-finite function. The proof uses Fourier inversion
for the first slot on each fixed choice of the remaining modes. It then
applies the induction hypothesis to the remaining slots.

`compactEquivariant_of_iteratedFourierMultiplier` applies this result to
two orders of a linear multiplier and a compact right translation.
The iterated Fourier coefficients use left rotations and commute with
right translation. The two compact restrictions consequently agree,
and uniqueness of the principal-series extension gives equality of
the standard vectors.

These are internal consequences of the Library's Fourier inversion and
compact principal-series model. They verify compact equivariance of
forward Fourier multipliers when these are passed through induction
in stages.
