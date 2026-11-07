# Compact finiteness of the spherical Laurent formula

This derived unit proves the compact-modulo-unipotent finiteness assertion for
`Langlands.Conductor.sphericalWhittakerPolynomial`. Its source motivation is
Jacquet, *A correction to Conducteur des représentations du groupe linéaire*
(2012), Section 2, printed p. 520, first paragraph. The formula itself and its
specialization to the explicit scalar spherical function come from
`Langlands.Representation.Conductor.SphericalPolynomial`. The identification
with a principal-series Whittaker function remains a separate obligation.

## Objects and assumptions

The field `F` has an arbitrary universe and is a nonarchimedean local field in
Mathlib's `IsNonarchimedeanLocalField` sense. Thus both zero and positive
characteristic are allowed. The rank is `n + 1`, a uniformizing element is
supplied, `q` is an explicit natural parameter, and `θ` is a complex unit-valued
character of the actual upper unipotent subgroup. Every finiteness assertion
assumes that `θ` is trivial on integral unipotent elements. No residue-cardinality
hypothesis on `q` is required for these assertions about the explicit formula.

`sphericalWhittakerValueSpan` is the complex submodule spanned by the Laurent
values on a specified subset of the actual general linear group. Its ambient
space is the existing symmetric Laurent subalgebra on `Fin (n + 1)` over `ℂ`.

## Implemented proof

Right integral invariance implies local constancy. Around `g`, use the open set
of `h` with `g⁻¹ * h` in the level-zero open subgroup. The published equality
between this subgroup and the integral subgroup makes the formula constant on
that neighborhood.

A locally constant map is continuous when its codomain is equipped with the
discrete topology. The image of a compact subset is therefore compact and
discrete, hence finite. This temporary topology serves only this proof; the
Laurent algebra acquires no global topology. `Module.Finite.span_of_finite`
then proves finite-dimensionality of its complex value span.

Left unipotent equivariance expresses the value at `u * c` as the complex scalar
`θ(u)` times the value at `c`. Consequently all values on the unipotent
saturation of a set lie in its value span. This algebraic membership lemma does
not require the field topology or the local-field hypothesis.

Finally, the actual left quotient is `LeftQuotient (upperUnipotent (n + 1) F)`.
The published compact-lifting theorem supplies a compact set `C` whose image is
a given compact subset `D` of that quotient. The upper unipotent subgroup is
closed by its matrix-entry equations. Local compactness of the general linear
group follows from local compactness of the finite matrix space and the topology
on its units. Hausdorffness of `F` is recovered using the compatible additive
uniformity of its valuative topology. If `g` lies above `D`, choose `c ∈ C`
with the same left coset. The quotient relation gives `g * c⁻¹` in the upper
unipotent subgroup, so the preceding membership lemma puts its value in the
finite-dimensional value span of `C`.

## Scope

The final theorem quantifies over every group element whose quotient image lies
in `D`. It proves finite-dimensional containment, rather than finite image on
that entire preimage: the character can vary along unipotent orbits. This unit
does not prove compactness of the support of a Rankin–Selberg integrand, a lower
bound on its determinant levels, coefficient integration, rational continuation,
or an essential-vector or conductor theorem. Those are further steps of the
corrected argument.
