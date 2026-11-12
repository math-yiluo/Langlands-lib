# Schur integral and the self orthogonality relation

Worker 89. This module supplies internal proof lemmas and the self relation used by
`Langlands.Renard.CompactRepresentation.schurOrthogonality`. The source target is
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, IV.3.3 Lemma (i), printed pp.101–102 / PDF pp.107–108.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implementation uses the two weak Schur forms separately rather than the
source's representation of the product group.

## Integrability without inversion invariance

`integrable_orthogonality_of_positiveForm` works modulo a supplied normal central
subgroup `A`. Both representations are square-integrable modulo `A`, with the
same supplied scalar action on `A`, and the second has an invariant positive
form. Compact-open cofinality and admissibility make
`InvariantPositiveForm.toSmoothDual` surjective. Expressing the second
functional as `b(z, -)` gives

`b(z, π₂(g⁻¹)v₂) = conjugate(b(v₂, π₂(g)z))`.

Thus the norm of the Schur integrand is the product of two forward coefficient
norms on `G/A`. The published square-integrability assumptions and Hölder's
inequality make that product integrable. Continuity of the descended Schur
integrand supplies its strong measurability. This lemma uses Haar measure but
does not need its right invariance.

## Scalar and positive formal degree

`orthogonalityIntegral_rho_left_rightInvariant` obtains the first Schur
invariance by translating on the right with the supplied right invariant
measure. `exists_leftSchurIntertwiner_rightInvariant` applies the published
admissible weak-form representation theorem. For the other Schur invariance,
the existing `exists_intertwiningMap_orthogonalityIntegral_right` uses left
Haar invariance.

`exists_schurScalar_rightInvariant` applies admissible Schur to both represented
forms for one irreducible admissible representation. Choose a nonzero vector
`v₀` and a smooth functional `ℓ₀` with `ℓ₀(v₀)=1`. The two scalarizations then
give a single scalar `κ`, independent of all four inputs:

`I(v₁, ℓ₁, v₂, ℓ₂) = κ * ℓ₂(v₁) * ℓ₁(v₂)`.

`exists_formalDegree_rightInvariant` uses an invariant positive form and a
nonzero vector `v`. With `ℓ=b(v,-)` and `r=Re(b(v,v))>0`, the diagonal integrand
is `|ℓ(π(g)v)|²`. Its real integral `s` is positive: the function is continuous,
nonnegative, and nonzero at the identity, and Haar measure is positive on
nonempty open sets. Scalarization gives `κ*r²=s`. Therefore `κ=s/r²` is
positive real; the implemented formal degree is `d=r²/s`.

## Essential square integrability and the full center

`schurOrthogonality_self` has the group, quotient measure and smooth-twist
hypotheses of the self half of the published statement. The previously proved
`essentiallySquareIntegrableAdmissible` supplies admissibility. The given twist
is then square-integrable in the published sense, and
`squareIntegrableUnitarySemisimple` supplies its invariant positive form.
Van Dantzig supplies compact-open cofinality.

Transport the two smooth functionals along
`smoothContragredientTwistEquiv`. Their underlying algebraic functionals are
unchanged. The factors `ω(g)` and `ω(g⁻¹)` cancel pointwise, so any function
`F` on the central quotient satisfying the target's coefficient identity is
the twisted Schur integrand. The preceding results give integrability and
the exact formula with `d>0`.

The generic helpers adapt the published
`HarishChandraSchwartz.SchurOrthogonality` constructions to an explicitly right
invariant measure. No inversion invariance is inferred from the Haar class.
The existing statement and proof modules remain unchanged.
