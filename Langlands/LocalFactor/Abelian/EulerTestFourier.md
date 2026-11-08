# Euler tests and their finite-place Fourier transforms

Worker 1692 constructs `PadicAbelian.eulerTest` for every supplied p-adic
topological field realization and every actual quasicharacter. This is internal
derived support for the global Hecke functional equation, using the published
local Euler-test, lattice Fourier and Gauss-transform results.

The test is the indicator of the integer ring for an unramified character,
and the inverse extended character on the integral units for a ramified
character. Its definition packages the published local constancy and compact
support proofs as a Schwartz–Bruhat function and uses the actual constructed
multiplicative conductor.

Multiplication by an integral unit multiplies the test by its inverse character
value. The plus Fourier transform has the opposite covariance, proved using
the actual Haar change of variables and the normalized absolute value one of
an integral unit.

For an unramified character the Fourier transform is the integer-ring mass
times the indicator of the additive-conductor lattice. In particular it fixes
the original test when the additive conductor is zero and that mass is one.
For a ramified character it is supported on the shell of order minus the sum
of the two conductors, with the explicit exponential, epsilon-at-zero and
extended-character factors of the published Gauss formula. No Haar
normalization or additive self-duality is assumed in these general formulas.

These results specialize and package the existing Library mathematics;
they do not prove the global functional equation or analytic continuation.
