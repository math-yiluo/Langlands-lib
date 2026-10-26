# Unitary twists of analytic coefficients modulo the full center

Author: Worker 429.

`Langlands.UnitaryTwistModCenterStatement.{uG,uV}` is a closed proposition.
For every topological group `G : Type uG`, every complex module `V : Type uV`,
every representation `ρ` of `G` on `V`, and every character `χ : G →* ℂˣ`
with open kernel and `‖χ(g)‖ = 1` for every `g`, it asserts

- `IsSquareIntegrableModCenter (twist χ ρ) μ` if and only if
  `IsSquareIntegrableModCenter ρ μ`;
- `IsTemperedModCenter (twist χ ρ) μ` if and only if
  `IsTemperedModCenter ρ μ`.

Here the quotient is the actual group `G ⧸ Subgroup.center G`. The statement
quantifies over a supplied measurable structure on this quotient, a proof that
it is Borel for the quotient topology, and every supplied Haar measure `μ`.
Each equivalence uses exactly the same measurable structure and measure on
both sides.

The predicates are imported unchanged. Square-integrability requires
admissibility and a genuine smooth unitary scalar central character `c` such
that, for every `ℓ : SmoothDual ρ` and every `v : V`, the descended coefficient
norm `c.coefficientNorm ℓ v` satisfies `MemLp … 2 μ`. Temperedness requires
admissibility and such a character with
`MemLp … (ENNReal.ofReal (2 + ε)) μ` for every smooth-dual functional, vector
and real `ε > 0`. Thus both strong measurability almost everywhere and finite
seminorm remain part of the assertions. Neither admissibility nor existence of
a central character is an extra premise.

The two universes are independent. There is no topology on `V`, dimension or
nonzero-carrier condition, irreducibility, reductivity, local compactness,
second countability or rank assumption. Existence of a Haar measure is not
asserted: the result concerns every measure carrying the displayed Haar
instance. The entire center is retained; no product decomposition or
factorization of representations is assumed.

## Internal provenance and intended proof route

This statement is an internal consequence proposed from existing Library
definitions and twist results. It is not attributed to an external
representation-theoretic theorem for arbitrary groups. Its inputs are:

- `Langlands.Representation.MatrixCoefficient.ModuloCenter`, defining the
  actual unitary central-character datum, descended coefficient norms and
  square-integrability;
- `Langlands.Representation.Classification.Tempered`, defining analytic
  temperedness with every positive epsilon;
- `Langlands.Representation.Twist.Definitions`, defining
  `(twist χ ρ)(g)v = χ(g) • ρ(g)v`.

The following is the intended route for a separate proof, not an implemented
proof in this module. The published `isAdmissible_twist_iff` transports
admissibility under the open-kernel assumption.
`smoothContragredientTwistEquiv χ ρ hχ` identifies the smooth-dual subtypes
and retains every underlying linear functional in both directions. Multiplying
the old central character by the restriction of `χ` to the actual center gives
the twisted scalar central action; intersecting their open kernels proves
smoothness. Linearity gives the pointwise coefficient identity
`ℓ((twist χ ρ)(g)v) = χ(g) * ℓ(ρ(g)v)`. The norm-one assumption then identifies
the coefficient norm functions on `G/Z`, so every displayed `MemLp` condition
is unchanged for the same measure and exponent. Applying this preservation
argument to the inverse character, using the published twist cancellation
laws, gives reflection.

The referenced transport results are in
`Langlands.Representation.Twist.AdmissibilityProof`,
`Langlands.Representation.Twist.SmoothPartDefinitions` and
`Langlands.Representation.Twist.AlgebraProof`. They explain why the generic
scope is appropriate; the statement imports only the existing predicates
and twist definition.

## Scope and status

This module defines the proposition and proves neither equivalence. It does
not prove the broad `GLSquareIntegrabilityPrerequisitesStatement`, Haar
uniqueness, duality, a single-coefficient criterion, preservation of Hermitian
forms, analytic continuation, occurrence of Jacquet constituents, exponent
bounds, multiplicity comparisons, or a Langlands quotient theorem.

The statement is a focused prerequisite for unitary slices of complex
product-Levi families. The supported all-regular comparison remains a separate
proof obligation.
