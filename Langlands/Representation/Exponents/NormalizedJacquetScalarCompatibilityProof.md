# Normalized Jacquet scalar compatibility

Authors: Worker 561, Worker 846 and Worker 438.

This module proves the published proposition
`Langlands.PadicField.TopologicalData.NormalizedJacquetScalarCompatibility.{uF,uV} T`
by `Langlands.PadicField.TopologicalData.normalizedJacquetScalarCompatibility`.
The theorem quantifies the prime, its primality instance, the actual p-adic
field and its topological data in the target's order, with independent field
and vector-space universes. Workers 561 and 846 supplied the shared proof
draft; Worker 438 separated its entry modules and checked the exact signatures.
These are internal algebraic calculations using the published quotient and
modulus, rather than a result quoted from original literature.

The helper
`Langlands.PadicField.TopologicalData.hasScalarCharacter_normalizedJacquet`
checks the scalar action on the actual quotient `B.JacquetModule ρ`.
Surjectivity of `B.jacquetMk` reduces an arbitrary class to the class of a vector
`v`. `T.normalizedJacquet_mk` expresses the normalized action as the inverse
square root of the positive Levi modulus times the class of the embedded
Levi action. At `B.scalarLevi F.Carrier a`, `T.leviModulus_scalar` makes this
normalizing scalar one, and `B.leviEmbedding_scalarLevi` identifies the
embedded matrix with `GeneralLinear.scalar a`. The assumed scalar action of
`ρ` and linearity of the quotient map give exactly multiplication by `ω a`
on the quotient.

The helper `Langlands.PadicField.TopologicalData.jacquetExponent_comp_const_eq`
handles every generalized split-centre character `χ`, without requiring an
open kernel. The imported `isGeneralizedEigencharacter_comp` restricts its
common-power equations along `Pi.constMonoidHom (Fin B.length) F.Carrierˣ`.
By the definitions of `T.splitCentreJacquet` and `B.scalarLevi`, the restricted
action is the normalized Jacquet action along ambient scalars. The scalar
action helper and `scalar_generalized_character_eq` identify the restricted
character with `ω`. The closing theorem pairs this result with the scalar
action conclusion in exactly the published target.

There is no nontriviality requirement on the Jacquet module: the scalar action
calculation holds on every quotient, and a generalized character already
supplies a nonzero vector whenever it occurs. In particular, zero Jacquet
modules are covered. No smoothness, finite dimension, finite length,
admissibility, continuity or open-kernel premise is added.

The module imports `ScalarGeneralizedEigencharacterProof`, which imports the
published statement. All arguments use elementary scalar algebra, the actual
coinvariant quotient, and the explicit block modulus. The result identifies
only restriction to the diagonal ambient centre. It identifies no individual
block character, constructs no Jacquet tensor equivalence, and proves no
segment norm formula. There is no dependence on analytic square-integrability,
Casselman criteria, derivative theorems or downstream classification.
