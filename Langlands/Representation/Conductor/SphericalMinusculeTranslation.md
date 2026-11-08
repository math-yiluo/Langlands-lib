# Weighted inverse minuscule translation of actual model vectors

This internal unit defines the finite weighted sum of inverse model translates.
Each inverse translate by `r` is multiplied by the inverse of
`determinantWeight abv r (0 - 1/2)`. At `g * r` its restricted model value is
therefore this scalar times the original model value at `g`.

The degree calculation uses an arbitrary field with a valuation into a linearly
ordered commutative group with zero and a supplied `IsUniformizingElement v ϖ`.
This means `v(ϖ) < 1` and every nonzero field valuation is an integer power of
`v(ϖ)`. The valuation of a matrix determinant is
`v(ϖ)` to the sum of its Iwasawa exponents, so that sum is additive under
matrix multiplication. Every labelled minuscule representative of index `k`
has exponent sum `k`. No character or residue-lift condition is needed for
these degree identities.

The weighted model operator itself requires a field with a topology, a unitary
additive character, a complex representation with a specified Whittaker
functional, an absolute value and a finite label type. Its definition does not
require smoothness or a finite-support assertion.

For the integrand identities, the valuation is `ValuativeRel.valuation F`.
Right translation on the actual left-unipotent quotient adds the sum of the
representative's Iwasawa exponents to its degree. This quotient calculation
assumes that the smaller general linear group is a topological group.

The finite-sum identities additionally require a positive natural number `q`,
`Fintype.card Λ = q`, and integral lifts `σ : Λ → F` that are distinct and
complete modulo the maximal ideal: `v(σ x - σ y) < 1` implies `x = y`, and
every integral `z` has some `x` with `v(z - σ x) < 1`. The unitary additive
character `ψ` is trivial on all integral elements. For every adjacent root of
the smaller group, some `x` satisfies `v(x) v(ϖ) ≤ 1` and the inverse standard
unipotent character takes a value different from one on `adjacentUnit i x`.
The field, valuation target, label type and representation space have independent
universes in the sections where they occur. There is no characteristic-zero or
local-field restriction on the field.

Write `D(g) = determinantWeight abv g (0 - 1/2)`, `Φ(g)` for the actual
spherical Laurent polynomial, and `W_r = D(r)⁻¹ π_model(rankInclusion 1 r⁻¹) W`.
The integrand before quotienting, evaluated at `g r`, is
`W(g) D(g) Φ(g r)`: nonvanishing of the determinant weight justifies the
cancellation. Summing over the actual labelled representatives and applying
`sphericalWhittakerMinusculeSum_eq` gives the normalized elementary scalar
`symmetricTorusHeckeScalar n q k` times the original integrand. Quotient
induction gives the same equality on the actual quotient.

For the degree-restricted integrand the precise identity is
`Σ_r I_d(W_r)(t r) = symmetricTorusHeckeScalar n q k * I_(d-k)(W)(t)`.
Every representative has degree `k`, so all indicator conditions agree; the
proof separates whether the original quotient point has degree `d-k`.
All sums are over `CosetIndex Λ (n+1) k`, including its full label multiplicity.

The provenance is internal. Determinant multiplicativity, the existing Iwasawa
decomposition, actual model action and labelled representatives supply the
degree and cancellation calculations; `SphericalHecke` supplies the finite
spherical identity. This unit does not integrate these equalities, establish
numerator stability or prove universal finite support, essential-vector
existence or any conductor assertion.
