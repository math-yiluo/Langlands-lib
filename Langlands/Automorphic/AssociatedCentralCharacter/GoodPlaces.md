# The Hecke character of `det S` at the good places of a weak association

Author: Worker 5151.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter` (module
`Langlands.Automorphic.AssociatedCentralCharacterProof`) shows: if `det S = δ ∘ τ_F` and
`S` is weakly associated with a spectral system `s` of rank `n`, then at cofinitely many
finite places `v` of `F` the character `δ` is unramified and its value `δ_v(ϖ_v)` at the
canonical uniformizer is `z_1 ⋯ z_n`, the top signed Euler coefficient of the spectrum
`{z_i}` of `s` at `v`. This is the unramified local computation behind Henniart (2000),
§2.2, `det S = ω_Π ∘ τ_F`, on the Galois side.

## `Langlands.Unramified.elementaryCoefficient_rank`

For `n` eigenvalues `s`, `elementaryCoefficient s n = ∏ z_i`. The Library defines
`elementaryCoefficient s k = (-1)^k · coeff_k (∏ (1 - z_i X))` (module
`Langlands.Representation.Unramified.HeckeOperators`); with
`Eigenvalues.eulerPolynomial_coeff_rank` the two signs cancel.

## `RelativeWeilGroup.finiteUniformizerValue_eq_prod_of_isUnramifiedMatchAt`

Hypotheses: `FundamentalClass.Restriction c`; `S` of rank `n` is an unramified match at `v`
for the Euler polynomial of the eigenvalues `z`; every place of `E` above `v` has
ramification index one; `δ` is unramified at `v`; and `det S = δ ∘ τ_F`. Conclusion:
`δ.finiteUniformizerValue v = ∏ z_i`.

Proof: take the place `w = placeAbove E v`. The unramified match supplies a local relative
Weil map `ι` for `w`, and `IsUnramifiedMatchAt.determinantCharacter_eq_prod` gives
`det S(ι Fr) = ∏ z_i`, with `Fr` the geometric Frobenius of `W_{F_v}`. Rewriting `det S`
as `δ ∘ τ_F`, the published `reciprocityCharacter_eq_finiteUniformizerValue` (module
`Langlands.ClassField.Global.RelativeWeilUnramifiedTwist`) evaluates
`(δ ∘ τ_F)(ι Fr)` as `δ.finiteUniformizerValue v`, since `Fr` has degree one
(`localGeometricFrobenius_degree`).

## `RelativeWeilGroup.eventually_finiteUniformizerValue_eq_elementaryCoefficient`

At an arithmetic class family `c`, if `S` is weakly associated with `s` of rank `n`
(`IsWeaklyAssociated S s`: `S` continuous, `S.rank = n`, and cofinitely many unramified
matches) and `det S = δ ∘ τ_F`, then for cofinitely many finite places `v`:
`δ.IsUnramifiedAt v`, `v ∉ s.exceptional`, and
`δ.finiteUniformizerValue v = elementaryCoefficient (s.eigenvalues v hs) n`.

Proof: the arithmetic family supplies `FundamentalClass.Restriction c`. Three cofinite
filters are intersected: the unramified matches of the weak association, the places of
`F` all of whose places above in `E` have ramification index one
(`eventually_ramificationIdx_eq_one`), and the complement of a finite set outside which `δ`
is unramified (`HeckeFunctionalEquation.exists_finset_isUnramifiedAt`). At such a place the
previous lemma and `elementaryCoefficient_rank` give the identity.
