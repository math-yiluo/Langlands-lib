# Operations and invariants of complex Weil representations

Worker 25 states a coherent family of properties of actual finite-dimensional
complex representations. `Langlands.Weil.RepresentationOperations` is the
conjunction of the five proposition definitions listed below. This module
states these propositions and proves none of them; it adds no axiom. The
separately published proofs are listed in
[Published proofs](#published-proofs).

The inputs are Mathlib representations on actual vector spaces. Their group
and three carrier universes are independent. Direct sum uses the binary
product carrier, tensor product uses the algebraic tensor product, and dual
uses the full algebraic linear dual. These carriers are finite-dimensional;
rank zero is allowed. The dual action is the transpose of the inverse action.
The scalar twist and its rank-one representation are reused from the exact
published `Langlands.Representation.Twist.Definitions` module.

## Declaration and source map

| Proposition | Content | Original source and derived content |
| --- | --- | --- |
| `RepresentationIsomorphismInvariance` | An actual invertible linear intertwiner preserves the group kernel, restricted inertia kernel, continuity, open inertia kernel, finite whole/inertia image, unramifiedness, irreducibility, semisimplicity, rank and determinant. | Tate section 2 opening, printed page 9/PDF18, represents objects up to isomorphism; all listed invariances are explicitly derived from conjugacy of action operators and the induced bijection on invariant subspaces. |
| `RepresentationRankDeterminant` | Ranks of sum, tensor and dual; determinants of sum, tensor, dual and scalar twist. | Tate section 2 opening, page 9/PDF18, uses determinant and dimension; Henniart 2002 sections 2.1–2.2, page 593/PDF7, use sums, tensor products and contragredients. The displayed formulas are elementary finite-dimensional consequences, not quotations of separate theorems in these passages. |
| `RepresentationExactSequenceInvariants` | Rank is additive and determinant is multiplicative in an actual short exact sequence of linear intertwiners. | Tate section 2 opening, page 9/PDF18, defines the exact-sequence additivity needed for virtual representations. The numerical and determinant identities follow from an adapted basis; a representation-theoretic splitting is neither assumed nor asserted. |
| `RepresentationOperationClosure` | Continuity, open inertia kernels, finite images, and unramifiedness are preserved by the relevant operations; duality and scalar twists preserve irreducibility and semisimplicity. | Tate section 2 opening/2.1, pages 9–10/PDF18–19, and section 4.1.2(a), page 20/PDF29; Henniart 2002 sections 2.1–2.2, page 593/PDF7. These are derived closure properties of the operations, not an assertion of block classification. |
| `RepresentationCharacterNormalization` | Every continuous action has a unique continuous unit-valued determinant character; every continuous rank-one action is isomorphic to exactly one continuous scalar-character representation. | Tate section 2 opening, page 9/PDF18, explicitly identifies rank-one isomorphism classes with quasicharacters by determinant. The Lean target quantifies the actual characters and linear equivalences. |

## Formulas and hypotheses

Write `d = dim V` and `e = dim U`. The formulas are

```
rank(V ⊕ U) = d + e,   rank(V ⊗ U) = d*e,   rank(V dual) = d,
det(ρ ⊕ σ)(g) = det ρ(g) * det σ(g),
det(ρ ⊗ σ)(g) = det ρ(g)^e * det σ(g)^d,
det(ρ dual)(g) = (det ρ(g))^-1,
det(χ ⊗ ρ)(g) = χ(g)^d * det ρ(g).
```

Twisting retains the carrier, so it retains rank by construction. For an exact
sequence, Lean requires injectivity of the first intertwiner, surjectivity of
the second, and equality of the first map's range with the second map's kernel.
It does not assume semisimplicity or a chosen complement.

Continuity uses `moduleTopology ℂ (Module.End ℂ V)`, the usual complex
finite-dimensional endomorphism topology. No topology on the carrier is
selected, and the complex scalars are not discrete. This is exactly the
predicate presentation of the published `Langlands.FiniteRepresentation.IsContinuous`
in `Langlands.Weil.Representation.Predicates`. Its `representation`
(from `Langlands.Weil.Representation.Basic`), `inertiaKernel`,
`HasOpenInertiaKernel`, `HasFiniteInertiaImage`, `HasFiniteImage`,
`IsUnramified`, `IsIrreducible` and `IsSemisimple` unfold to the expressions
in this target. The target is stated on these underlying Mathlib objects and
does not import that bundle, so it introduces no competing bundle. The bundle's
own rank invariance under linear equivalence,
`FiniteRepresentation.rank_eq_of_equiv`, and the descended
`FiniteRepresentation.classRank` on its isomorphism quotient are already in
`Basic`; this family adds determinant and property invariance.

The closure target assumes a topological group, as continuity of the inverse
action is needed for duals and openness of larger subgroups is used for
inertia kernels. The subgroup `I` need not be open, compact, normal, or
nonarchimedean for these closure implications. Those stronger hypotheses
belong to the separate continuity-comparison target. A continuous character
alone is not used to infer an open inertia kernel: openness of the restricted
character kernel is an explicit hypothesis in that clause. Finite-image
claims require finite image of both factors. No converse is asserted for
tensor products or general twists, where cancellation or a zero carrier
would invalidate one.

Duality reflects continuity, kernel openness, finite image, unramifiedness,
irreducibility and semisimplicity in finite dimension. The twist clauses
preserve irreducibility and semisimplicity for every unit-valued character;
they do not require that character to be continuous or unitary. Continuity
of the twisted action has its own explicit hypothesis.

The rank-one statement is an existence-and-uniqueness assertion about a
character, with an actual representation equivalence as its property.
No classification witness is assumed in a structure field. This is a
parameter-side normalization interface; it is not local reciprocity or
the local Langlands correspondence.

## Published proofs

Every proposition of this family is proved, outside this module, at
independent universes. The theorems are in namespace `Langlands.Weil`:

| Theorem | Proves | Module after `Langlands.Weil.Representation.` |
| --- | --- | --- |
| `representationIsomorphismInvariance` | `RepresentationIsomorphismInvariance.{uG, uV, uU}` | `IsomorphismInvarianceProof` |
| `representationRankDeterminant` | `RepresentationRankDeterminant.{uG, uV, uU}` | `RankDeterminantProof` |
| `representationExactSequenceInvariants` | `RepresentationExactSequenceInvariants.{uG, uV, uU, uT}` | `ExactSequenceProof` |
| `representationOperationClosure` | `RepresentationOperationClosure.{uG, uV, uU}` | `OperationClosureProof` |
| `representationCharacterNormalization` | `RepresentationCharacterNormalization.{uG, uV}` | `CharacterNormalizationProof` |
| `representationOperations` | `RepresentationOperations.{uG, uV, uU, uT}` | `OperationsProof` |

`representationOperations` is the conjunction of the five component theorems,
in the order of the conjunction.

## Exact sources and dependencies

- Tate, *Number theoretic background*, Corvallis Part II (1979),
  section 2 opening and 2.1, printed pages 9–10/PDF18–19, and section
  4.1.2(a), printed page 20/PDF29. Literature ID
  `tate-1979-number-theoretic-background`; retained `Part II.pdf` SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)* (2002), sections 2.1–2.2, printed page 593/PDF7. Literature ID
  `henniart-2002-characterization`; source SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- Accepted twist definition artifact
  `c83db975-8b79-4fbb-9901-2db836910a0a`, version 1; published commit
  `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`; Lean SHA-256
  `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
  Previously published twist composition, intertwiner and dual-twist
  identities are reused as infrastructure and are not restated here.
- Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
  Lean 4.34.0, Mathlib commit
  `5ed2965256430c3649e86755f9576b54eca72435`, where the family was first
  stated. The current check environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
  uses the same Lean version and Mathlib commit.
  The mathematical interfaces are `Representation.prod`, `tprod`, `dual`,
  `Equiv`, `IntertwiningMap`, `Module.finrank`, `LinearMap.det`,
  `Representation.IsIrreducible` and `IsSemisimpleRepresentation`.

No project definition is copied from the companion `Basic` and `Predicates`
modules, which were an unpublished draft when this family was stated and are
now published. Their Mathlib carrier/action interface determines the
compatibility described above.
This family does not construct an actual local Weil group or supply WD
monodromy, Frobenius semisimplification, block classification, or arithmetic
L/epsilon/gamma identities. Those remain distinct assigned families.
