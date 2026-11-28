# Compactly supported spectral tests under a local displacement

Proposition 7.8 in Delorme's spectral theorem takes a boundary value by moving the imaginary spectral parameter by a small real displacement. A compact test permits the displacement to be chosen uniformly even when the representative and its coefficient functions are regular only on an open neighborhood of the imaginary plane.

`CompactSpectralDisplacementStatement` considers a compactly supported complex test on a real normed space and a weight defined as a function of a real displacement and the spectral variable. The weight is used on an open set containing the product of zero displacement with the topological support of the test. A globally defined product agrees with the weighted test for all sufficiently small displacements and vanishes off the same spectral support. It inherits continuity or smoothness when the test has that regularity and the weight has it on the open set.

The proof takes a tube about the compact support and inserts a smooth cutoff in the displacement variable, equal to one near zero. The support of the product before multiplication by the weight lies in the given open set. Near all other points the product vanishes. This gives the claimed global regularity and permits the smooth family to be used in the Fourier boundary calculation.

`compactSpectralIntegral_tendsto` applies the continuous form with a measure finite on compact sets. The slice at zero is absolutely integrable, and the integral of the compactly supported family is continuous at zero. Restricting the neighborhood filter gives the limit through positive displacements.

The boundary-value application is in Patrick Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics **426** (2023), 109107, Proposition 7.8 and its proof, p. 33.
