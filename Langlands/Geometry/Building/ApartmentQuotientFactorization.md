# Common apartments and two-point subgroup factorization

This internal unit gives an algebraic test for the existing quotient's
common-apartment condition. It uses the published
`ApartmentQuotient.HasCommonTranslatedApartment` without introducing another
geometric predicate.

For any group `H`, subgroup `N` acting on an apartment type `A`, and covariant
subgroup family `P`, `exists_common_apartment_iff_factorization` identifies a
common translated apartment for `apartment P x` and `g • apartment P y` with
the factorization `g = p * n * q`, where `p ∈ P x`, `n ∈ N`, and `q ∈ P y`.
No reductive group, valuation or building axiom is assumed.

In the forward direction, equality of quotient representatives supplies two
normalizer corrections `n` and `m`. The left factor is `h * n`, the middle
factor is `n⁻¹ * m`, and the right factor is `(g⁻¹ * h * m)⁻¹`. The quotient
relation places the outside factors in the required subgroups. In the reverse
direction, elements of `P x` and `P y` fix the corresponding quotient points.
The translate by `p` of the base apartment therefore contains both points,
with apartment coordinates `x` and `n • y`.

`hasCommonTranslatedApartment_iff_factorization` quantifies this equivalence
over all `x`, `y` and `g`. Every quotient point has a translated apartment
representative; translating a pair by the inverse of its first group
representative reduces to the previous result.

The Prop-valued `CommonApartmentFactorizationStatement` states this
equivalence universally, allowing independent universes for `H` and `A`.
`commonApartmentFactorization` proves that exact proposition.

The provenance is the published quotient relation and its action and
stabilizer lemmas. This unit proves the equivalence, not either side for a
particular valued root datum. For the actual building quotient the remaining
algebraic obligation is `G(k) = P_x N(k) P_y` for every pair of apartment
points. No common-apartment existence or maximal-boundedness theorem is
claimed.
