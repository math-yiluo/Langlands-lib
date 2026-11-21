# Proper parabolic induction cannot be irreducible and square-integrable

Let `F` be a bundled `PadicField` with topological realization `T`. All
representations use the actual groups on `F.Carrier` and the topology of
`T`. The theorem
`Langlands.PadicField.TopologicalData.isEmpty_equiv_smoothInduced_of_squareIntegrable`
proves that an irreducible `T.IsSquareIntegrable` representation of `GL_n`
is not isomorphic to the unnormalized smooth induction of any smooth Levi
representation inflated to a standard block parabolic with at least two
blocks. The field, square-integrable carrier, and inducing carrier universes
are independent. No separate admissibility assumption is imposed on either
representation. At rank zero or one the condition on the block shape cannot
hold.

## Reduction to normalized induction with a scalar character

An inducing isomorphism would transfer irreducibility and admissibility to
the unnormalized induction; `T.IsSquareIntegrable.isAdmissible` gives the
admissibility of the original representation. The theorem in
[`BlockInducingRecovery`](../Representation/Induction/BlockInducingRecovery.md)
then gives irreducibility and admissibility of the Levi representation `Ξ`.
Let `δ_P^{1/2}` denote the Library's half-modulus. Twisting `Ξ` by the inverse
of the Levi half-modulus gives an irreducible admissible `σ`: the twisting
character has open kernel. Normalized induction of `σ` is isomorphic to
unnormalized induction of `Ξ`, since after inflation to the parabolic the
inverse half-modulus twist cancels the positive half-modulus in the normalized
covariance law. The code proves equality of the two inducing representations
of the parabolic and applies `Induction.smoothInducedEquiv`. The same recovery
module gives a block-scalar character `χ` of `σ` with open kernel.

## The contradiction for normalized induction

`not_squareIntegrable_normalizedParabolicInduced` is the normalized form of
the obstruction, for admissible `σ` with a supplied block-scalar character
`χ` with open kernel. The Library's `exists_isRealPartOf` expresses its
absolute value as the product of powers of the normalized absolute values
on the block scalar coordinates. Write `x` for the vector of real powers. The
private `induction_scalar_cone` applies the Library's proved
[`squareIntegrableInductionEmbeddingCone`](../Representation/Exponents/SquareIntegrableInductionEmbeddingConeProof.md)
to the normalized induction itself. In the universe required by the cone
theorem, it uses the natural equivalence to induction of a `ULift` of `σ` as
an embedding. `ULift` preserves the block-scalar equation; irreducibility
supplies the nontriviality of the source. Thus `x` belongs to the strict
positive root cone: its total sum is zero and every proper, nonempty initial
sum is positive.

Next apply
[`Parabolic.naturalNormalizedInductionDuality`](../Representation/Parabolic/NaturalInductionDualityProof.md)
to identify the smooth contragredient of the induced representation with
the normalized induction of the smooth contragredient of `σ` **along the
same parabolic**. The former is irreducible by admissible smooth duality.
It is also square-integrable. For this step,
`isSquareIntegrableModCentralSubgroup_center_iff` identifies the Library's
arbitrary-central-subgroup square-integrability predicate at the full center
with the existing modulo-center predicate: the two coefficient norms agree
on quotient representatives. For each Haar measure on the central quotient,
the `GL_n` central-quotient results give right invariance, hence inversion
invariance together with left invariance. With the compact open subgroup
basis, the Library's contragredient square-integrability theorem then applies.
It uses admissible biduality and inversion of matrix coefficients. This
proves `isSquareIntegrable_smoothContragredient` in exactly the same `T`.

The contragredient of `σ` has block-scalar character `χ⁻¹`: its action on a
smooth functional at a block scalar is precomposition with the inverse
action of that scalar. Taking reciprocals in the absolute value identity
and using `Real.rpow_neg` gives the real-part vector `-x`. The same cone
theorem now puts `-x` in the strict positive root cone. As the block count
is at least two, the initial sum of length one is strictly positive for
both `x` and `-x`. Their sum is zero, a contradiction.

## Sources and scope

This is a derived application of Casselman's criterion, not a separate
classification of square-integrable representations. See W. Casselman,
*Introduction to the theory of admissible representations of p-adic
reductive groups*, draft 1 May 1995 (`casselman-1995-admissible-representations`),
§1.4 (p. 13) and Theorem 4.4.6 (pp. 44–45) for the weak chamber and strict
decay off the compact torus units times the split center, and §3.1,
Proposition 3.1.2 (p. 32) and Theorem 3.2.4 (p. 34) for the normalization,
same-parabolic duality, and first adjointness. The imported cone proof
already combines first adjointness and the strict criterion on the block
scalars. The two cone applications here replace a direct application of the
criterion to the Jacquet exponents of the induced representation and its dual.
The conclusion excludes an isomorphism to the **whole** induction, not
subquotient occurrence in an induction. It supplies the non-induction clause
needed at `σ = 1` in Henniart–Lemaire 2011, II.1.7 (printed p. 59).
