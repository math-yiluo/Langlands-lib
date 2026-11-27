# Residue fields and the label fields

The label sets of `Labels` record polynomials over the fields
`polarExtensionField (labelFieldSize q) D`, the model of `𝔽_{q^D}`. This
module compares them with the residue fields of local fields.

- `natCard_polarBaseField` and `natCard_labelField`: for a prime power
  `q` and `D ≥ 1`, the base field has `q` elements and the label field
  `q^D` elements.
- `nonempty_ringEquiv_labelField`: a finite field with `q^D` elements is
  isomorphic to the label field (`FiniteField.ringEquivOfCardEq`).
- `jacobsonResidueField`, `natCard_jacobsonResidue`,
  `finite_jacobsonResidue`: for a nonarchimedean local field `F`, the
  quotient of `𝒪[F]` by its Jacobson radical (the residue ring used by
  `Stratum.fundamentalPolynomial`) is a finite field with `q_F` elements.
- `natCard_spectralJacobsonResidue`: for a finite extension `E/F` with its
  spectral structure, the corresponding residue field of `E` has
  `q_F^{f(E|F)}` elements, `f(E|F) = subfieldResidueDegree F E`.

## Proof of the last statement

`subfieldResidueDegree F E` is the inertia degree of the maximal ideal of
the integral closure of `𝒪[F]` in `E`
(`PureApproximation.subfieldResidueDegree_eq_inertiaDeg`), i.e. the
dimension of its residue field over `𝒪[F]/𝔭_F`. It is positive since
`e f = [E:F]`, so the residue field is finite-dimensional and has
`q_F^{f(E|F)}` elements (`Module.natCard_eq_pow_finrank`). The isomorphism
`subfieldIntegerEquiv F E` with `𝒪[E]` carries the maximal ideal to the
Jacobson radical of `𝒪[E]`.

Source: Bushnell–Kutzko 1994,
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, the notation
`𝔍(M, q)` and (1.13), printed p. 115, which do not distinguish
isomorphic finite fields.
