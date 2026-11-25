# Finite isolation on the existing product-induced smooth sections

This derived module implements finite parameter isolation directly in the torus
coordinates of the existing packet section space. Its source motivation is
Waldspurger VIII.4.2, printed p.330 (PDF p.96), where a section is chosen with
one specified coefficient and zero values at the other classes in the finite
central-character fiber.

For a finite group acting by injective translations on a finite circle torus,
`exists_smoothFiniteTorusFunction_invariant_finiteValues` takes finitely many
parameters, a target parameter, and the hypothesis that none of the selected
parameters is in the target's stabilizer orbit. It constructs a smooth scalar
equal to one at the target and zero at the selected parameters, invariant under
all stabilizer translations.

The proof enlarges the finite set by all stabilizer translates and the target
orbit, then applies the published coordinate Lagrange interpolation theorem.
The sum of its translates is smooth and invariant by reindexing the finite
group. At the target, only the identity translate contributes, because the
translation homomorphism is injective. At every selected parameter all terms
vanish by the stated separation hypothesis. No division or measure
normalization is involved.
`SmoothInvariantFiniteInterpolationStatement` records this precise scalar
interpolation proposition, proved by `smoothInvariantFiniteInterpolation`.

`exists_mem_productInducedSmoothOrbitSections_finiteValues` first uses the
published prescribed-value theorem to obtain a section with the required
actual product-induced fiber value. It multiplies that section by the
constructed scalar using the published smooth-section multiplication theorem.
The result belongs to the original coherent smooth orbit-section space, takes
the prescribed value at the target parameter, and is zero at every selected
parameter. The theorem assumes the actual finite class stabilizer and uses
the packet's own torus coordinates, with no coordinate change.

The generic section theorem retains all compact-picture, continuity,
factorization, smoothness and finite-stabilizer inputs of the existing
section interface. It proves no packet membership or cuspidality theorem, and
neither the Waldspurger VIII.4.2 cuspidal coefficient equality nor the
same-level coefficient lifting.
