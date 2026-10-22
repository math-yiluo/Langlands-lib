# Conjugating geometric pieces equal whole-Levi transport

Author: Worker 289.

## Result and scope

`Langlands.CuspidalSupport.associatedGeometricPieceEquivalence` proves exactly
`Langlands.CuspidalSupport.AssociatedGeometricPieceEquivalenceTheorem.{uF,uV}`
from the published `AssociatedGeometricPiecesStatement` module. Its telescope
quantifies every implicit prime `p` with `Fact p.Prime`, every actual
`F : PadicField.{uF} p`, compatible `T : F.TopologicalData`, and natural rank
`n`. The field and input-carrier universes are independent. The final unapplied
constant assignment checks this complete telescope.

The proposition retains every published component parameter: block shapes
`B C`, the smooth representation, its quasicuspidality hypothesis, association,
the minimal representative, both refinements, both complete intersection
refinement hypotheses, and the whole-Levi conjugation hypothesis. Its
conclusion is a `Nonempty` actual `Representation.Equiv` from precisely the
published `geometricPieceFunctor` object to `transport B C w.val hw` of the
input. All ranks, including zero, and the zero representation are covered.

The proof uses the Levi equalities from the intersection refinement hypotheses
and the conjugation hypothesis. Quasicuspidality, association, minimality and
the other intersection equalities are retained in the target but are not
needed for this equivalence. The proof does not assume a geometric lemma,
a filtration, irreducibility, admissibility, finite length, or a nonzero input.
Neither the published statement pair nor any imported pair is changed.

## Implemented proof

First, `sourceLevi_eq_top_of_conjugates` and
`targetLevi_eq_top_of_conjugates` show that both intersection Levis are full.
The source inclusion follows directly from the equality of conjugated ambient
Levis. The target inclusion uses the already constructed inverse whole-Levi
conjugation and its matrix embedding formula. The refinement equalities thus
make both refined Levis full.

For any full refined Levi, `refinedParabolic_eq_top_of_refinedLevi_eq_top`
uses its actual inclusion section to show that its parabolic is full.
`refinedLeviProjection_val_of_full` applies the projection-section identity
to the same ambient element, so the projection preserves its value.
The projection kernel description then proves
`refinedUnipotent_eq_bot_of_full`: the actual radical is the trivial subgroup.

For normalization, fullness of the product parabolic implies fullness of each
inner parabolic by inserting an arbitrary matrix in a single product
coordinate. The imported
`block_indices_subsingleton_of_parabolic_eq_top` proves that each inner block
index type is a subsingleton. Consequently no ordered pair of distinct inner
blocks contributes to the explicit modulus formula. The inner products and
then their outer product are one. This proves
`refinedModulus_eq_one_of_full`, and the positive and inverse half characters
also evaluate to one. No interpretation of this character as Haar scaling is
required in this argument.

`fullRefinedJacquetEquiv` constructs the quotient-to-input linear map by
lifting the identity through the actual coinvariant quotient. Each relation
vanishes because its group element belongs to the trivial radical. Its inverse
is the canonical quotient map. Quotient surjectivity proves one inverse law;
the other holds on representatives. The normalized action formula and the
proved inverse-half-modulus identity establish intertwining. Thus both
Jacquet maps are constructed, rather than supplied as hypotheses.

For induction, `fullInductionInverse` sends a vector `v` of an ambient smooth
representation `τ` to the actual covariant function
`x ↦ e.symm (τ x v)`, where `e` identifies the coefficient action with the
restriction of `τ`. Intertwining proves covariance. A single open subgroup
fixing `v` fixes this entire function on the right, which proves the required
uniform smoothness. `fullInductionEquiv` evaluates at one and applies `e`.
When the inducing subgroup is full, covariance determines the entire function
from that value, proving the first inverse law. The identity action proves the
second. Right translation and covariance establish equivariance.
`fullRefinedInductionEquiv` applies this construction to the normalized refined
inducing representation. It removes the character using the proved positive
half identity and removes the projection using its proved value formula.
The coefficient equivalence is a generic helper parameter; the closing proof
constructs it from the preceding Jacquet and transport maps.

`subgroupEqualityEquiv` handles both literal subgroup-equality functors by
equality elimination. `intersectionLeviConjugation_symm_val` compares inverse
intersection conjugation with inverse whole-Levi conjugation: their images
under the injective source embedding have the same permutation-matrix
formula. `intersectionTransportFullEquiv` retains the linear equivalence of
coefficients and uses this equality to prove compatibility of the actions.

Finally the closing theorem follows the actual functor composite in order:
normalized refined Jacquet, source equality relabeling, intersection transport,
target equality relabeling, and normalized refined induction. The ambient
target is the published whole-Levi transport. Its smoothness follows from
`isSmooth_transport`. The final equivalence is the constructed induction
evaluation equivalence with all its coefficient maps instantiated by the
preceding constructions.

## Provenance

This is a derived proof of the individual-piece identification already stated
in `AssociatedGeometricPiecesStatement.md`. The motivating original is
I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 2.11–2.12, printed p. 448 / PDF p. 9, define the individual composite
functors, and Corollary 2.13(c), printed p. 449 / PDF p. 10, uses the
whole-Levi transport pieces for associated Levis. Those two pages were read
directly for this proof. The implementation gives the full-refinement maps
explicitly; it proves neither the geometric filtration nor the separate
quasicuspidality or vanishing components.
