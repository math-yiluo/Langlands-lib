# Regularization of a unitary smooth-vector functional

For a continuous smooth-vector functional `ℓ`, use the Hilbert Riesz
identification on the bounded functional given by first averaging with the
conjugate-inverted kernel and then applying `ℓ`. Conjugation in both operations
makes the resulting map complex-linear in the original kernel. The Gårding
estimates of `GardingFunctionals` and the smoothness theorem of `GardingRiesz`
construct these bounded functionals and show that their Riesz vectors are smooth.

Moving group translations through the averaged orbit gives left covariance
and the conjugate Whittaker multiplier for the right translations. Equality
of two regularizations gives equality of the functionals first on the Gårding
averages and then on all smooth vectors by density for the genuine
word-derivative topology. Scalar proportionality follows by conjugate
linearity in the first argument of the Hilbert pairing.

This construction implements the regularization used in Shalika (1974), §3,
with the conventions of the Library's Whittaker functional.
