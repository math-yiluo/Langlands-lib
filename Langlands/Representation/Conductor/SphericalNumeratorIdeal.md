# The ideal of actual finite spherical numerators

This internal unit constructs the ideal structure on the actual numerator
image from `SphericalLinearity`. It proves closure of that existing image
under every symmetric Laurent multiplier, and applies the established weak
Nullstellensatz conditionally on pointwise nonvanishing.

The algebraic preliminary results apply to any field `K` and finite coordinate
type, including the empty type. `torusPolynomialAlgebraMap_injective` uses that
the coordinate product in the polynomial ring is nonzero, so localization at
its powers is injective. `symmetricTorus_exists_polynomial_numerator` clears
the denominator of a symmetric Laurent polynomial. Its polynomial numerator
is symmetric: apply each coordinate permutation to the clearing identity,
use symmetry of the original element and of the coordinate product, and use
injectivity to compare polynomial numerators.

`symmetricTorus_subalgebra_eq_top` proves that any `K`-subalgebra of the
symmetric Laurent algebra containing all elementary symmetric polynomials
and the inverse coordinate product is the whole algebra. Mathlib's
`esymmAlgHom_surjective` expresses the symmetric polynomial numerator in the
elementary generators. Polynomial induction puts its image in the given
subalgebra. Multiplying it by the required power of the inverse coordinate
product recovers the original Laurent polynomial.

`submoduleMultiplierSubalgebra U` is a general construction for a submodule
of a commutative semiring algebra. Its elements are precisely the `b` such
that `b*a` belongs to `U` for every `a` belonging to `U`. The submodule axioms
prove additive closure and scalar closure, and repeated multiplication proves
multiplicative closure.

The model section treats an arbitrary nonarchimedean local field `F` with its
valuative relation and topology, and a smooth complex representation `π` of
`GL_(n+2)(F)` with specified Whittaker functional `ℓ`. The group of rank
`n+1` and its upper unipotent subgroup have measurable structures and Borel
instances, and the unipotent quotients in rank `n+1` and rank one have
measurable structures. Neither irreducibility nor a nonzero-functional
hypothesis is needed. The field, representation-space and finite-label
universes are independent.

The supplied `h : IsJacquetNormalization q ψ abv ϖ μ` specifies the residue
cardinality, uniformizing unit, absolute value, conductor of the unitary
additive character and actual compatible quotient measure, and supplies the
quotient Borel instances. In particular, the uniformizer has valuation less
than one and its integral powers realize all nonzero field valuations;
`abv(ϖ) = q⁻¹`, and `abv` is one on valuation units. The character is trivial
on the integers and an element annihilating all integral multiples under the
character is itself integral.

The model results retain the explicit finite-sum inputs of
`SphericalMinusculeCoefficient`:

- `q > 0` and a finite type `Λ` with cardinality `q`;
- integral lifts `σ : Λ → F` that are distinct modulo the maximal ideal,
  meaning `v(σ x - σ y) < 1` implies `x = y`, and cover every integral residue;
- for each adjacent root, an `x` with `v(x)*v(ϖ) ≤ 1` at which the inverse
  standard unipotent character is different from one.

Here `v` is the canonical valuation. These witnesses are inputs, with no
restriction to a particular local field. The denominator polynomial `P` is
arbitrary; no standard-factor or nonzero-polynomial condition is used.

`mul_mem_corankOneModelNumeratorSubmodule` applies the generation theorem to
the multiplier subalgebra of the actual numerator submodule. The established
minuscule action puts every elementary symmetric generator in that
subalgebra. The established central action supplies the inverse determinant
by taking its integer exponent to be minus one. Thus all symmetric Laurent
multipliers preserve the actual image.

`corankOneModelNumeratorIdeal` uses exactly the carrier of
`corankOneModelNumeratorSubmodule`, with this multiplication theorem supplying
the ideal axiom. It is not constructed by taking an ideal span.
`mem_corankOneModelNumeratorIdeal_iff` records that membership is equivalent
to an actual coefficient-model vector `w`, finiteness of the actual support
of its product with the coordinate denominator from `P`, and equality of the
sum of those coefficients to the prescribed numerator.

`corankOneModelNumeratorIdeal_eq_top_of_no_common_zero` assumes that at every
unit tuple there is an actual finite-support model vector whose numerator
evaluates nontrivially there. These witnesses meet the hypothesis of
`symmetricTorusIdeal_eq_top_of_no_common_zero` over the algebraically closed
field of complex numbers. Consequently the actual numerator ideal is the
whole ring. `exists_corankOneModelNumerator_eq_one_of_no_common_zero` uses
membership of one and the exact membership equivalence to obtain a single
actual finite-support model vector with numerator one.

The provenance is internal: the arguments combine localization and the
fundamental theorem of symmetric polynomials with the existing actual
minuscule and central model actions, their numerator identities, and the
proved symmetric Laurent weak Nullstellensatz. This unit does not establish
pointwise nonvanishing, universal finite support, a standard L-polynomial,
the essential-vector identity or any conductor conclusion. Those remain
separate obligations for `EssentialConductorStatement`.
