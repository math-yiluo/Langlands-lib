# Internal positive powers and polar factors

Author: Worker 1571.

This internal auxiliary module uses the Hermitian spectral theorem to define
positive real powers of a positive definite matrix unit. Its diagonal powers
are the construction in `AlgebraicMatrixPowers`; no matrix logarithm is used.
The proof of preservation of polynomial subgroup equations is inherited from
that module and `PositivePowerPolynomial`.

`positivePower g hg r` conjugates the positive eigenvalue powers by the
unitary spectral basis of the value matrix of `g`. The spectral theorem makes
the power at exponent one equal to `g`. Positive diagonal entries and
invariance of positive definiteness under invertible adjoint conjugation
prove positive definiteness at every real exponent. The real-power addition
identity proves the multiplication law and makes the power at exponent one
half square to `g`.

`positivePower_mem` applies `conjugatedPower_mem` to keep these powers inside
an explicitly polynomially defined subgroup. `exists_positive_sqrt` packages
the power at exponent one half with membership, positive definiteness and
the square identity. These are auxiliary results, not the actual reductive
Iwasawa existence theorem. Actual-point algebraicity, a compatible
self-adjoint realization and the parabolic covering remain obligations.
