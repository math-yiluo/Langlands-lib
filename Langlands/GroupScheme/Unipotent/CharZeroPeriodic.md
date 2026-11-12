# Periodic vectors of unipotent linear maps in characteristic zero

This is an internal derived linear algebra helper for the connectedness proof
for unipotent algebraic groups in characteristic zero. It does not assert that
the connectedness theorem has been proved.

For a linear endomorphism of a vector space over a field of characteristic zero,
finite order implies semisimplicity: the endomorphism is annihilated by the
separable polynomial `X^n - 1`, where `n` is nonzero. This argument works without a
finite-dimensionality hypothesis. The implementation reuses the published
`Langlands.BlockSumParameter.isSemisimple_of_pow_eq_one` from
`Langlands.Weil.Local.BlockSumParameter`.

If the difference of the endomorphism and the identity is also nilpotent, that
difference is both semisimple and nilpotent and is therefore zero. These steps
use Mathlib's separability, semisimplicity under scalar translation, and
nilpotent semisimple endomorphism theorems.

The vector version assumes only `(f^n) x = x` and `((f - 1)^m) x = 0`,
with `n` nonzero; it concludes `f x = x`. The proof restricts `f` to the
invariant subspace `ker(f^n - 1)`. Its restriction has finite order and is
therefore semisimple. The given vector is in its generalized eigenspace for the
eigenvalue `1`, so semisimplicity makes it an ordinary eigenvector. No uniform
nilpotence exponent on the whole ambient vector space is needed.
