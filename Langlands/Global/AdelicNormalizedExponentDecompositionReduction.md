# Normalized exponent decomposition from Harish-Chandra finiteness

`adelicNormalizedExponentDecompositionReduction` derives the finite normalized
decomposition of an automorphic function on a parabolic quotient from
`ParabolicHarishChandraFinitenessStatement`. It applies at any maximal compact
with the stated Iwasawa coverage. The ordinary decomposition is provided by
`exists_exponentDecomposition_of_parabolicHarishChandraFiniteness`.

Subtract the half-modulus parameter from each ordinary exponent. The
translation is a bijection on parameters, so relabelling the finite set
preserves the sum and leaves each automorphic component as it was.
`hasExponent_iff` identifies its ordinary exponent with the resulting
normalized label. This is the normalization in Delorme's (3.2).

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 5–6 and 10, §2 and (3.2).
