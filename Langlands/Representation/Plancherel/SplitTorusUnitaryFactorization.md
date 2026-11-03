# Unitary-times-positive factorization on actual split tori

For an actual split torus over an arbitrary-universe nonarchimedean local field,
`unitaryFactor hA χ` is the character
`χ * (positiveCharacter hA (normalizedRealPart hA χ))⁻¹`.
The product of this factor and that positive character is exactly `χ`.
Both field characteristics and every torus rank, including zero, are allowed.
The construction uses the existing actual rational points, real character space
and positive valuation.

The algebraic product, inverse and positive-character recovery laws show that
the normalized real part of this factor is zero. For a smooth `χ`, the
intersection of its open kernel with the positive character's open kernel lies
in the factor's kernel, which is consequently open. The all-point
zero-parameter-if-and-only-if-unitary theorem then proves
`‖(unitaryFactor hA χ a : ℂ)‖ = 1` at every actual point `a`.
This uses the proved compact-kernel norm formula and assumes neither
unramifiedness nor a norm-one property of `χ`.

`smoothUnitaryFactorization` bundles this actual character with its open-kernel
proof, its pointwise norm-one proof and the product identity recovering `χ`.
Its value is definitionally `unitaryFactor hA χ`.
All openness statements use exactly `rationalPointTopology F A.X`. The explicit
affine instance follows from splitness by `IsSplitTorus.isAffineHom` and
`isAffine_of_isAffineHom`; split smoothness supplies the finite-type instance
inside the proof making the actual point group topological.

This is a derived implementation of the unitary-times-positive decomposition
in Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, V.3.19–V.3.20 (printed pp.115–116/PDF pp.121–122;
registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The positive factor uses the source's normalized exponential convention
`q ^ (-pair(phi, ν(a)))`. The separately named raw logarithmic parameter
evaluates to `log ‖χ(a)‖` and equals `(-log q) • normalizedRealPart hA χ`.
These two source normalizations retain their exact scalar difference.
