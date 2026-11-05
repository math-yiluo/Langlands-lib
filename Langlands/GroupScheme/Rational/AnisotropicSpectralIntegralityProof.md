# Spectral integrality for anisotropic reductive groups over local fields

The theorem `anisotropicSpectralIntegrality` proves exactly
`Langlands.GroupScheme.AnisotropicSpectralIntegralityStatement.{u}`.
For every actual nonarchimedean local field `F : Type u`, connected reductive
group scheme `G` over `F` with split rank zero, natural number `N`, and actual
representation `ρ : MatrixRepresentation G (Fin N)`, every characteristic
coefficient of every actual matrix `ρ.rationalMatrix g` satisfies `coeff ≤ᵥ 1`.
This is membership in the valuation ring of the given valuative relation.
The dimension includes zero, and the coefficient index is unrestricted.

This is an internal assembly of the imported actual factorization and
integrality constructions. Reductivity supplies affineness and smoothness
of the structure morphism; smoothness supplies local finite type.
`positivePowerFactorizationData G g` then supplies a strictly positive
exponent, an actual closed torus inclusion, an actual rational torus point,
and an actual additive-group morphism. The chosen positive power of `g`
is the product of the torus point's image and that morphism's value at
additive coordinate one, and the two factors commute.
The factorization construction works over every field; its
positive-characteristic branch permits imperfect fields.

The proof passes those data directly to
`MatrixRepresentation.charpoly_coeff_vle_one_of_pow_eq_torus_mul_additive`.
That imported result restricts anisotropy to the closed torus and uses
independent anisotropic torus compactness to contain the torus factor's
powers in a compact set. The additive factor's powers lie in a continuous
image of the compact valuation unit ball. Commutation combines these sets
into compact containment for the powers of the specified positive power
of `g`. Continuity of the actual representation bounds its matrix powers;
the finite-lattice argument makes the matrix integral over the valuation
ring. Integrality descends through the positive exponent to
`ρ.rationalMatrix g`, and the integral-matrix coefficient theorem and
integral closure of valuation integers give the displayed bound.

The closing theorem has the unchanged published statement as its type,
at arbitrary universe `u`. It imposes no faithfulness, chosen splitting,
compactness, boundedness, eigenvalue, or representation semisimplicity
premise. General anisotropic reductive compactness is not an input to this
proof; the separate spectral boundedness criterion remains a separate result.
