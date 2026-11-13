# The top coefficient of an Euler polynomial

Author: Worker 5151.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter` (module
`Langlands.Automorphic.AssociatedCentralCharacterProof`) reads the determinant of a
relative Weil representation at a Frobenius element off the top coefficient of its local
Euler polynomial.

## `Langlands.LocalFactor.eulerPolynomial_coeff_finrank`

For an endomorphism `A` of a finite-dimensional complex space `V` of dimension `n`, the
coefficient of `X^n` in the Euler polynomial `det(1 - X A)` is `(-1)^n det A`. The Euler
polynomial is the reverse of the characteristic polynomial (`eulerPolynomial`); its `X^n`
coefficient is the constant coefficient of `charpoly A` (`coeff_reverse`, `revAt_le`, with
`charpoly_natDegree = n`), which is `(-1)^n det A` by Mathlib's
`LinearMap.det_eq_sign_charpoly_coeff`; the two signs cancel since `(-1)^(2n) = 1`.

## `Langlands.Unramified.Eigenvalues.eulerPolynomial_coeff_rank`

For `n` nonzero numbers `s = {z_1, …, z_n}`, the coefficient of `X^n` in
`∏ (1 - z_i X)` is `(-1)^n ∏ z_i`. Writing `s` as a tuple (`ofTuple_surjective`,
`eulerPolynomial_ofTuple`), each factor has degree at most one, so Mathlib's
`coeff_prod_of_natDegree_le` gives the top coefficient as the product of the `X`
coefficients `-z_i`; `Finset.prod_neg` extracts the sign and `List.prod_ofFn` identifies
the product with the multiset product.

## `RelativeWeilGroup.determinantCharacter_eq_prod_of_localEulerPolynomial`

If `S` has rank `n`, `ι : W_{F_v} → W_{E/F}` is continuous, and
`localEulerPolynomial S ι` (the Euler polynomial of `S(ι Fr)`, with `Fr` the geometric
Frobenius of `W_{F_v}`) is the Euler polynomial of `n` eigenvalues `s`, then
`det S(ι Fr) = ∏ z_i`. Comparing `X^n` coefficients of both sides by the two lemmas above
gives `(-1)^n det S(ι Fr) = (-1)^n ∏ z_i`, and `(-1)^n` is cancelled.

## `RelativeWeilGroup.IsUnramifiedMatchAt.determinantCharacter_eq_prod`

If `S` of rank `n` is an unramified match at `v` for the Euler polynomial of `s`
(`IsUnramifiedMatchAt S v s.eulerPolynomial`), then for every place `w` above `v` and every
local relative Weil map `ι` for `w` (`IsLocalRelativeWeilMap v w e ι`), `det S(ι Fr) = ∏ z_i`:
the match supplies `localEulerPolynomial S ι = s.eulerPolynomial`, and the previous lemma
applies.
