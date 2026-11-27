# Subunitarity of normalized exponents on Siegel split rays

`AdelicSiegelExponentSubunitarityStatement` takes a finite normalized exponent
decomposition with logarithmic Siegel chamber growth. Fix a point of the positive
split component whose ambient image is a Siegel torus point and whose nonnegative
integral powers stay in the specified chamber. Every nonzero component has normalized
exponent of modulus at most one at that point.

Submultiplicativity bounds the logarithm of the matrix height on the ray by an affine
function of the integer parameter. The Siegel half-modulus comparison identifies
the square root of the modulus with the corresponding power of the parabolic half
modulus. The estimate therefore satisfies the hypotheses of
`norm_parameterPower_le_one_of_ray_bound`. In particular the argument applies to the
fundamental Siegel rays for simple roots omitted from the Levi index.

The source is the necessity argument of P. Delorme, *On the spectral theorem of
Langlands*, Advances in Mathematics 426 (2023), 109107, Proposition 3.6, PDF p. 13.
The registered PDF is `Delorme--On the spectral theorem of Langlands--2023.pdf`,
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`,
under `delorme-2023-spectral-theorem-langlands`.
