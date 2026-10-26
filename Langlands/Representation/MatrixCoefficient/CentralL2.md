# The actual square-integrable central-character model

Author: Worker 88.

This internal construction uses the published `Induction.CentralFunctions`,
`centralInduced` and `centralNorm` with their positive covariance
`f(zg) = χ(z) f(g)` and right action `f(xg)`. The group universe is arbitrary.
The character has complex unit values of norm one.

`centralPairing` descends `conj(f(g)) * h(g)` to the full central quotient.
Neither complex-valued covariant function is individually descended.
Covariance and `conj(χ(z)) * χ(z) = 1` prove well-definedness.
The pairing is locally constant for the quotient topology. Its norm is the
product of the real quotient norms and its diagonal is the complex image of
the real norm square. Conjugate symmetry, left additivity, conjugate scalar
linearity and the simultaneous right-translation identity are proved on
quotient representatives.

For a Borel measure `μ`, `centralL2Submodule` consists exactly of actual
centrally covariant smooth functions whose `centralNorm` satisfies `MemLp`
at exponent two. The triangle inequality and constant multiplication prove
submodule closure. Holder's inequality for the two real quotient norms and
the exact pairing-norm identity prove `centralPairing_integrable`.
`centralL2_norm_sq_integrable` also records integrability of the real
norm-square itself.

If `μ` is right invariant, `centralL2Subrepresentation` proves stability by
composition with measure-preserving right multiplication on the quotient.
`centralL2Representation` restricts the existing action, and
`centralL2Inclusion` is an injective equivariant inclusion with exact
evaluation laws. Smoothness is inherited from the original functions'
uniform open right stabilizers.
`centralL2_ext` recovers equality from pointwise evaluation, and
`centralL2Inclusion_recover` recovers each original function when it is
equipped with the required `MemLp` proof.

With the additional assumption `μ.IsHaarMeasure`, `centralL2Form χ hχ μ`
constructs an actual `Langlands.InvariantPositiveForm` of that restricted
representation. Its value is the Bochner integral of `centralPairing`.
The pointwise conjugate-symmetry, additivity and conjugate scalar identities,
together with the proved integrability, give the corresponding integral
identities. The diagonal has nonnegative real part. The form includes
conjugate scalar linearity in its first argument; the explicit
`centralL2Form_inner_add_right` and `centralL2Form_inner_smul_right` laws
give complex linearity in its second argument.

Definiteness is proved on actual functions. If the diagonal integral
vanishes, the nonnegative integrable real diagonal vanishes almost
everywhere. Haar positivity on nonempty open sets and continuity of this
locally constant function imply that it vanishes everywhere, using
Mathlib's `Measure.eq_of_ae_eq`. Evaluation on every quotient representative
then gives zero norm-square, hence zero original complex function.
No definiteness hypothesis or quotient by almost-everywhere equality is
introduced.

The existing simultaneous-translation law for the pairing and right
invariance of `μ` prove invariance of the integrated form.
`centralL2Form_inner` exposes the exact complex integral.
`centralL2Form_inner_self` identifies its diagonal with the complex image
of the real integral of `centralNorm` squared.

The construction accepts any Borel Haar measure on the actual quotient
`G / Subgroup.center G` together with its explicit
`Measure.IsMulRightInvariant` instance. Once that measure is supplied,
Mathlib's Haar class already provides the open-set positivity needed here,
so the construction requires no further local-compactness or Hausdorff
instance on the quotient. In particular, locally compact Hausdorff
quotients are included. No second countability, compactness of the quotient,
triviality of the character or finite-dimensionality is assumed.

This constructs the central L2 pre-Hilbert model only. Coefficient-map
restriction, Hilbert completion, smooth-vector recovery, construction of a
right-invariant measure on the actual GL quotient, discrete-component
theorems, mirabolic decomposition and genericity remain separate work.

## Provenance

This is an internal derivation from the published CentralInduction pair,
the existing smooth-induced representation and Mathlib's Lp, Bochner
integration and Haar measure APIs. No external theorem of unitary
decomposition or genericity is used.
