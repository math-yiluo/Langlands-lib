# Realization of finite smooth presentations in the spectral family space

`exists_smoothCompactFamily_of_finite_forms` realizes a finite combination of
square-integrable inducing forms with smooth compactly supported coefficient
functions in each component of `spectralFamilySpace`. The positive Weyl counts
make the weighted spectral measures finite on compact sets. The theorem takes
square integrability of the individual Iwasawa restrictions as input.

The proof forms the weighted `L²` class of each inducing function and sums those
vectors with the prescribed coefficients. Continuity and compact support give
square integrability of each summand for the scaled spectral measure. The
almost-everywhere equality for the resulting family uses the equality of null
sets of the scaled and original spectral measures. The corresponding identity
for the weighted Iwasawa restriction follows from the finite-sum restriction
lemma.

This is an internal construction using `spectralFamilySpace` and
`IsSmoothCompactFamily`, in the finite-family realization of Arthur's inducing
Hilbert spaces in *An introduction to the trace formula* (2005), §7, p. 35
(volume PDF p. 47), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
