# Euler coefficient of an actual section cokernel

`SectionCokernelEulerCoefficientStatement` is an internal numerical bridge for
line-bundle Euler polynomials. Let `X` be an integral Noetherian separated scheme
proper over a field `K`, with topological Krull dimension at most `d + 1`. Let
`L` be an actual line bundle and `s` a global section of its actual `n`th tensor
power whose generation open is nonempty. Write `Q` for the actual categorical
cokernel of `sectionHom (tensorPow L.obj n) s`.

For any finite-affine-section witness `hQ`, if `Q` has support dimension strictly
less than `d + 1`, the statement asserts

`coeff d (coherentEulerPolynomial f Q hQ L d) =
 (d + 1) * n * coeff (d + 1) (lineBundleEulerPolynomial f L (d + 1))`.

The products and coefficients are rational. The polynomials are the existing
Newton polynomials of the actual proper coherent Euler sequences. Quasi-coherence
of the structure module, the actual line-bundle power, and its section cokernel
is supplied by the existing rank-one and cokernel closure results. The witness
`hQ` can also be obtained by the existing quotient closure theorem; it is retained
as an argument to permit the caller's chosen witness.

This is derived content. The nonempty generation open on an integral scheme gives
the actual short exact sequence `0 → O_X → L^n → Q → 0`. Tensoring by each
`L^m` and taking actual Euler characteristics gives the difference
`χ(Q ⊗ L^m) = χ(L^(m+n)) - χ(L^m)`. The dimension and support bounds identify
these sequences with their existing Euler polynomials. Uniqueness on natural
arguments identifies the polynomial of `Q` with the translation difference of
the polynomial of `L`. The coefficient formula is the existing rational
`shiftDifference_coeff` identity. These published constructions and elementary
arithmetic justify the statement without an additional literature assertion.

No ampleness, positive exponent, exact support dimension, or positivity premise
is required. In particular `n = 0` and `d = 0` are included. This statement is a
supporting identity; it supplies neither its proof nor the host ample positivity
theorem. Worker 689 specified the interface and its role in the integral step.
