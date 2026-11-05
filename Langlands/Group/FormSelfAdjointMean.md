# Geometric means of self-adjointness forms

Author: Worker 1359.

This module works with matrix groups over an arbitrary `RCLike` field `𝕜`. It
proves that two positive definite forms for which a polynomially defined
subgroup is self-adjoint have a geometric mean that is again such a form.
From this it derives a real version: a conjugation-stable subgroup that is
self-adjoint for some positive definite form is self-adjoint for one fixed by
entrywise conjugation. It is one step of a planned route to a self-adjoint
matrix realization of a reductive group. It does not prove that realization.

## Definitions

- `IsFormSelfAdjoint A J`: for a subgroup `A` of `GL n 𝕜` and a matrix unit
  `J`, every `g ∈ A` has `J⁻¹ * star g * J ∈ A`. Here `star` on a matrix
  unit is the conjugate transpose (over the reals, the transpose). This is
  the same form condition as the hypothesis `hform` of the published
  `Langlands.GroupScheme.MatrixRepresentation.exists_closed_starStable_of_positiveForm`,
  with `A` the range of the rational points.
- `conjCoordinate a` and `invConjCoordinate a`: substitutions that express
  the matrix entries and inverse entries of `x * a * x⁻¹` and `x⁻¹ * a * x`
  as polynomials in the coordinates of `x`. They are built from the generic
  matrix and generic inverse of `Langlands.GroupScheme.GeneralLinear`.
- `conjGL : GL n 𝕜 →* GL n 𝕜`: entrywise conjugation `starRingEnd 𝕜`
  applied to matrix units. Over the reals it is the identity.

## Results

Elementary facts about units:

- `star_eq_self_of_posDef`: a positive definite unit is fixed by `star`.
- `posDef_inv`: the inverse of a positive definite unit is positive definite.
- `posDef_star_mul_self`: `star x * x` is positive definite for every unit `x`.
- `posDef_mul_mul_of_star_eq`: if `star c = c` and `J` is positive definite,
  then `c * J * c` is positive definite.
- `positivePower_zero` and `positivePower_neg_mul`: the spectral power with
  exponent `0` is `1`, and exponent `-r` gives the inverse of exponent `r`.

Polynomiality of normalizers:

- `eval_conjCoordinate`, `eval_invConjCoordinate`: evaluating the
  substitutions at `x` gives the coordinates of `x * a * x⁻¹` and
  `x⁻¹ * a * x`.
- `aeval_bind₁`: if the substitution `σ` evaluated at `x` gives the
  coordinates of `y`, then evaluating `bind₁ σ p` at `x` is evaluating `p` at
  `y`.
- `isPolynomiallyDefined_normalizer`: the normalizer
  `Subgroup.normalizer (A : Set (GL n 𝕜))` of a polynomially defined
  subgroup `A` is polynomially defined.

Geometric means:

- `isFormSelfAdjoint_star_mul_self`: if, for every `g`,
  `x⁻¹ * g * x ∈ A` implies `x⁻¹ * star g * x ∈ A`, then `A` is self-adjoint
  for `star x * x`. This turns the conclusion of
  `Langlands.Group.MinimalVector.exists_conj_star_mem_stabilizer` (a separate
  submitted module, not imported here) into a form.
- `inv_mul_mem_normalizer`: if `A` is self-adjoint for positive definite `h`
  and `h'`, then `h⁻¹ * h'` normalizes `A`.
- `conj_positivePower`: `c * positivePower g hg r * c⁻¹` is the conjugated
  diagonal power family `conjugatedPower` for the unit `c * U`, where `U` is
  the eigenvector unitary of `g`.
- `exists_mean` (main theorem): let `A` be polynomially defined and
  self-adjoint for positive definite `h` and `h'`. Then there is a positive
  definite `X` with `X * h⁻¹ * X = h'` for which `A` is self-adjoint.
- `eq_of_mul_inv_mul_eq`: for positive definite `h`, the equation
  `X * h⁻¹ * X = h'` has at most one positive definite solution `X`.

Real forms:

- `conjGL_val`, `conjGL_conjGL`, `conjGL_star`: `conjGL` conjugates every
  entry, is an involution and commutes with `star`.
- `posDef_conjGL`: `conjGL J` is positive definite when `J` is.
- `isFormSelfAdjoint_conjGL`: if `A` is stable under `conjGL` and
  self-adjoint for `J`, then it is self-adjoint for `conjGL J`.
- `exists_real_form` (main theorem): let `A` be polynomially defined, stable
  under `conjGL`, and self-adjoint for a positive definite `J`. Then there is
  a positive definite `m` with `conjGL m = m` for which `A` is self-adjoint.
  So every entry of `m` equals its own conjugate, and `m` is a real
  symmetric positive definite matrix.

## Proof

Normalizers. For `x` in the normalizer and a defining polynomial `p` of `A`,
the polynomials `bind₁ (conjCoordinate a) p` and
`bind₁ (invConjCoordinate a) p`, for `a ∈ A`, vanish at `x`. Conversely, if
all these polynomials vanish at `x`, then `x * a * x⁻¹ ∈ A` and
`x⁻¹ * a * x ∈ A` for every `a ∈ A`, which is membership in the normalizer
by `Subgroup.mem_normalizer_iff`. The second family gives the reverse
implication `x * a * x⁻¹ ∈ A → a ∈ A`, applied with `a` replaced by
`x * a * x⁻¹`.

`inv_mul_mem_normalizer`. Write `τ_J g = J⁻¹ * star g * J`. Since `star h = h`
and `star h' = h'`, a direct computation gives
`τ_h (τ_h' a) = (h⁻¹ * h') * a * (h⁻¹ * h')⁻¹`. Applying `τ_h` and then
`τ_h'` to `(h⁻¹ * h') * a * (h⁻¹ * h')⁻¹` gives back `a`. Both maps send `A`
into `A`, which gives the two directions of normalizer membership.

`exists_mean`. Let `s = positivePower h hh (1/2)`, so `s * s = h` and
`star s = s`. The unit `q = s⁻¹ * h' * s⁻¹` is positive definite. Let
`p = positivePower q hq (1/2)`, so `p * p = q`. By `conj_positivePower`,
`s⁻¹ * positivePower q hq r * s` is the family `conjugatedPower (s⁻¹ * U) λ hλ r`,
where `U` is the eigenvector unitary and `λ` the eigenvalues of `q`.
At `r = 1` it is `s⁻¹ * q * s = h⁻¹ * h'`, which lies in the normalizer by
`inv_mul_mem_normalizer`. The normalizer is polynomially defined, so the
published `Langlands.Group.AlgebraicMatrixPowers.conjugatedPower_mem` puts
the value at `r = 1/2`, namely `z = s⁻¹ * p * s`, in the normalizer. Set
`X = s * p * s`. It is positive definite, and

    X * h⁻¹ * X = s * p * s * s⁻¹ * s⁻¹ * s * p * s = s * q * s = h'.

Also `X = h * z`, so for `g ∈ A`,
`X⁻¹ * star g * X = z⁻¹ * (h⁻¹ * star g * h) * z`. The middle factor is in
`A`, and `z⁻¹` normalizes `A`.

`eq_of_mul_inv_mul_eq`. Let `s` be the square root of `h` as above. If `X`
solves the equation, then `W = s⁻¹ * X * s⁻¹` is positive definite and
`W * W = s⁻¹ * (X * h⁻¹ * X) * s⁻¹ = s⁻¹ * h' * s⁻¹`. Two positive definite
`W` with the same square are equal by Mathlib's
`CFC.mul_self_eq_mul_self_iff`, using the matrix order of `MatrixOrder`. Then
cancelling `s⁻¹` on both sides gives `X = Y`.

`exists_real_form`. A positive definite `J` is Hermitian, so `conjGL J` is
the transpose of `J`, hence positive definite (`posDef_conjGL`). For `g ∈ A`,
`(conjGL J)⁻¹ * star g * conjGL J = conjGL (J⁻¹ * star (conjGL g) * J)`,
which lies in `A` because `A` is `conjGL`-stable and self-adjoint for `J`. So
`exists_mean` applies to `h = J` and `h' = conjGL J` and gives `X` with
`X * J⁻¹ * X = conjGL J`. Applying `conjGL` gives
`conjGL X * (conjGL J)⁻¹ * conjGL X = J`. Inverting the first equation gives
`X * (conjGL J)⁻¹ * X = J`. So `X` and `conjGL X` are positive definite
solutions of the same equation, and `eq_of_mul_inv_mul_eq` gives
`conjGL X = X`. Take `m = X`.

## Provenance and scope

The statements and proofs are internal. Geometric means of positive definite
matrices are classical, but no statement is taken from the literature. The
library inputs are the published spectral powers of
`Langlands.Group.AlgebraicPolar`, `conjugatedPower_mem` and
`IsPolynomiallyDefined` from `Langlands.Group.AlgebraicMatrixPowers`, and
Mathlib.

Intended use: in the real case of
`Langlands.GroupScheme.ConnectedReductiveSelfAdjointRealizationStatement`,
take for `A` the complex points of a real group in `GL n ℂ`. They are
polynomially defined by real polynomials and stable under conjugation.
Suppose a positive definite form for `A` is known, for example from a minimal
vector through `isFormSelfAdjoint_star_mul_self`. Then `exists_real_form`
gives a real positive definite form. The remaining steps are not proved here:
comparing real points with conjugation-fixed complex points, and normalizing
through `exists_closed_starStable_of_positiveForm`.
