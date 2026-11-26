# Uniqueness and automorphy of weak constant terms

`eq_zero_of_sum_eq_zero_of_hasExponent` uses the directness of the Library's unnormalized
exponents. Translation by the half-modulus parameter is a bijection of the parameter space.
`hasExponent_iff` makes the translated labels the unnormalized exponents, so a zero finite sum
has zero components.

`sum_filter_eq_of_hasExponent` extends two finite expansions to the union of their supports by
assigning zero to absent labels. The terms of their difference retain their normalized
exponents. Directness forces each difference to vanish, so summing over any common predicate
on the labels gives equality. `IsWeakConstantTerm.unique` uses the predicate `Re λ = 0`.
`IsWeakConstantTerm.isAutomorphicOn` uses closure of the automorphic submodule under the finite
sum of the unitary components of an exponent decomposition.

Source. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See uniqueness in (3.2), p.10,
and the unitary partial sum of Definition 3.7, p.13.
