# Euler comparison at the distinguished completion

`CompletedPairDistinguishedEulerComparisonStatement` compares an indexed finite
family of lower standard-additive cuspidal pair factors with one upper pair over
an extension of number fields. The presentations have irreducible admissible
finite components, with compact adelic additive quotients over both fields. Fix
a finite place `v₀` with one place `w₀` above it. Supply the completed equation
for each lower pair and the upper pair, with their exceptional sets, forward
and dual Gamma block lists and constant unit multipliers. Each lower finite
epsilon factor must be one outside its own exceptional set.

Assume both lower polynomials at `v₀` are one for each family member. At each
other place the forward lower product must match the forward product over the
upper places, and the same must hold for the dual products. If the upper forward
and reflected dual polynomials at `w₀` have disjoint roots under `x ↦ q_w₀⁻¹ / x`,
both upper polynomials at `w₀` are one.

Triviality of the lower epsilon factors outside their own exceptional sets
allows enlarging those sets to their union before multiplying the equations.
Concatenating the Gamma block lists gives the corresponding Gamma factors. The finite
epsilon multipliers are continuous and nowhere zero because they are products of
Laurent monomials in the nonzero local spectral variables. Regroup each upper Euler
product by the place below. At `v₀`, multiply the single factor by its polynomial
denominator. That denominator is nonzero on the chosen right half-plane because the
upper Euler product has a nonzero limit. The resulting products and the local root
separation give the hypotheses of `distinguishedEulerFromEquations`.

This is an internal reduction for the finite Euler comparison in the proof of
Arthur–Clozel, Chapter 1, Proposition 6.9(ii), printed p. 70 (PDF p. 84). It uses
the two completed equations there and certifies the remaining finite Euler comparison
from local root separation.
