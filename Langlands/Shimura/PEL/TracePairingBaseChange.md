# Scalar extension of the normalized PEL trace pairing

Worker 57. This derived internal construction extends the published rational
trace pairing to an arbitrary commutative rational algebra S. It uses the
actual tensor algebra S tensor over Q with A and Mathlib's bilinear-form
base change; it takes no new form or comparison theorem as input.

`regularTrace_tmul` extends the published `regularTrace_one_tmul` identity
to a general pure tensor by linearity in its first factor. Its hypotheses
retain a finite free original scalar module.

`tracePairingBaseChange` is exactly the base change of `D.tracePairing beta`.
The pure-tensor formula is the defining base-change identity. For arbitrary
x and y, `tracePairingBaseChange_apply` identifies the form with

```text
map_Q,S(1/n) Tr_S(L_(x (1 tensor beta) sigma_S(y))).
```

Here Tr is the regular trace, sigma_S is the actual extended rational
involution, and n is the central-simple degree. The proof derives rational
finite dimensionality from the actual algebra, reduces both arguments by
tensor induction, and applies the pure-tensor regular-trace formula.
The normalization is the one already established in `Unitary.RationalTrace`.

For a skew unit beta, the module proves skew-symmetry and alternation of
this actual extended form. The skew identity follows by tensor induction
from the rational skew identity. Rational multiplication by one half
then proves alternation, including when S has zero divisors. These two
results retain the E-to-K-to-A scalar tower of the imported rational
skew identity; the trace formulas and twist cancellation do not need it.

Finally `skewTwist_tracePairingBaseChange_apply` extends the inverse-unit
form of the auxiliary algebra with involution tau = beta sigma beta inverse.
The result simplifies to

```text
map_Q,S(1/n) Tr_S(L_(x sigma_S(y) (1 tensor beta inverse))).
```

The proof checks the actual base-changed involution by tensor induction
and cancels the two adjacent units. This is an identity for every skew
unit, independent of positivity.

The provenance is internal: the imported `TracePairing`, `PositiveInput`
and `RationalTrace` provide the source-normalized rational form, its skew
identity, the auxiliary algebra and trace compatibility. The new content
is their scalar-extension calculation. This module proves no Hodge
polarization sign, nondegeneracy after scalar extension, adelic group
comparison, integral lattice existence or moduli representability.
