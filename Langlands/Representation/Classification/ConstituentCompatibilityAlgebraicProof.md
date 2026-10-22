# Algebraic compatibility of irreducible constituents

Author: Worker 34.

The closing theorem
`Langlands.Classification.allPadicGLAlgebraicConstituentCompatibility`
proves exactly the published proposition
`Langlands.Classification.AllPadicGLAlgebraicConstituentCompatibility`
from `ConstituentCompatibility`. The representation-carrier universe `uV`
and field universe `uF` are independent. The published statement, its
Markdown, and all imported modules are unchanged.

This is an internal algebraic proof of the derived structural targets
documented in [ConstituentCompatibility.md](ConstituentCompatibility.md).
It does not invoke a classification theorem or assert that an irreducible
head, socle, or central character exists. The source conventions and
literature boundaries remain those of the published statement and
[ConstituentRelations.md](ConstituentRelations.md). No new assertion from
the original literature is used here.

## Generic theorems

All declarations below are in `Langlands.Classification`.

| Declaration | Scope and conclusion |
| --- | --- |
| `twistConstituentCompatibilityFor` | For every group `G`, proves `TwistConstituentCompatibilityFor G`: common twisting preserves and reflects irreducible quotient, subrepresentation, head, and socle relations. |
| `constituentIsomorphismUniquenessFor` | For every group `G`, proves `ConstituentIsomorphismUniquenessFor G`: two irreducible heads of one representation are equivalent, and so are two irreducible socles. |
| `glConstituentCentralCharacterFor` | For every field `F` and natural number `n`, proves `GLConstituentCentralCharacterFor F n`: the prescribed character passes to constituents, and a determinant twist multiplies it by the character's `n`th power. |
| `allPadicGLAlgebraicConstituentCompatibility` | Specializes these three generic results to every prime, every `PadicField`, and every positive rank. |

The carriers in the constituent predicates all lie in one arbitrary universe,
as required by the published definitions. There are no finite-dimensionality,
topology, smoothness, admissibility, or source-irreducibility hypotheses.
The scalar-character transfer lemmas require only a surjective or injective
intertwiner, not irreducibility. The general-linear theorem also holds for
`n = 0`; the exact closing target only asks for positive ranks.

## Implemented proof

For quotients and subrepresentations,
`isIrreducibleQuotient_twist_iff` and
`isIrreducibleSubrepresentation_twist_iff` use the published
`Langlands.isIrreducible_twist_iff`. The constructors
`twistIntertwining` and `untwistIntertwining` retain the underlying linear map,
so the same surjectivity or injectivity proof witnesses the constituent
relation after transport.

For heads, `IsIrreducibleHead.of_twist` first reflects the relation from a
common twist. It untwists the selected quotient map. Given any irreducible
quotient of the original source, it twists that quotient and its quotient
map, then applies the assumed uniqueness of kernels. Both relevant linear
maps remain unchanged, so this is the required equality of kernels in the
original source. `isIrreducibleHead_twist_iff` obtains preservation by applying
reflection with the inverse character to the twisted representations;
the published `twist_inv_twist` identifies the double twists with the original
representations. Thus the uniqueness quantifier still tests every
irreducible representation in the specified carrier universe.

`IsIrreducibleSocle.of_twist` and `isIrreducibleSocle_twist_iff` use the same
argument with injective intertwiners and equality of their image subspaces.
These four equivalences are packaged by `twistConstituentCompatibilityFor`.

For uniqueness, the proof reuses Worker 23's published canonical constituents.
Given two irreducible heads, `nonempty_headEquiv` supplies equivalences
from `head ρ` to each; the inverse of the first followed by the second is the
desired equivalence. For socles, `nonempty_socleEquiv` supplies equivalences
from each socle constituent to `socleRepresentation ρ`; the first followed
by the inverse of the second gives the conclusion. No choices of additional
constituents or extra existence assumptions are introduced.

For a scalar character along any homomorphism `z : C →* G`,
`HasScalarCharacter.of_surjective` writes a target vector as the image of a
source vector and uses intertwining and linearity to push the scalar action
through the surjection. `HasScalarCharacter.of_injective` applies the injection
to the desired identity, then uses intertwining, the known scalar action,
and linearity. The first two clauses of
`glConstituentCentralCharacterFor` apply these lemmas to the scalar-matrix
homomorphism and the maps witnessing the constituent relations.

For its last clause, evaluation of the twist at a scalar matrix gives
`χ (det (z I_n)) • ρ (z I_n) v`. The prescribed action of `ρ` replaces the
second factor by `ω z • v`. Mathlib's
`Matrix.GeneralLinearGroup.det_scalar` gives `det (z I_n) = z ^ n`.
Homomorphism evaluation, the cardinality of `Fin n`, scalar associativity,
and commutativity in `ℂ` yield `(ω * χ ^ n) z • v`, with the rank factor
retained.

The closing proof introduces the prime, field, rank, and positive-rank
hypothesis of the exact target and supplies the three generic theorems.
The stronger generic results make no use of primality or positivity.

## Dependencies and verification boundary

Besides the target module, the direct project imports are
`Classification.CanonicalConstituents`, `Twist.SubquotientProof`, and
`Twist.AlgebraProof`. They supply the canonical equivalences, irreducibility
invariance, and inverse-twist cancellation used above.

Development uses the prepared Lean 4.34.0 environment with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation and declaration
inspection are development checks. Independent semantic review, machine
exact-target validation, and Library publication are separate requirements.
