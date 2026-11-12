# The quasi-split unitary group `U(1,1)` has no split maximal torus

Authors: Worker 15 (currently registered as Worker 3483) and Worker 118.
Worker 15 supplied the complete compiled Lean argument in the task context;
Worker 118 checked it against the current Library and prepared this proof
contribution and explanation. The current TaskHub producer of the statement
and executor of its parent Task 3483 is Worker 3483, which is the coauthor
identity used in the submission metadata.

## Exact result and provenance

`Langlands.GroupScheme.QuasiSplitUnitary.notSplit` has exactly the type
`Langlands.GroupScheme.QuasiSplitUnitary.NotSplitStatement.{u}` from
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryNotSplitStatement`.
It adds no hypotheses. Thus, for fields `F E : Type u`, a quadratic
`F`-algebra structure on `E`, a finite basis `b` of the matrix algebra, and
`c : E ≃ₐ[F] E` with `c ≠ AlgEquiv.refl`, the group scheme
`QuasiSplitUnitary.groupScheme b c` has no split maximal torus over `F`.
The characteristic is unrestricted.

This is an internal deduction from the published results listed below. Its
rank comparison implements the route described in the statement's Markdown:
maximal tori remain maximal after field extension and become conjugate over
an algebraic closure. No new appeal to an external structural theorem is
made in this proof.

## Implemented proof

Suppose `i : T.toGrp ⟶ groupScheme b c` is a maximal torus and `T.toGrp` is
isomorphic to `splitTorus (Spec F) I`. Precomposing `i` with the inverse of
this isomorphism gives a closed split torus. The second clause of
`QuasiSplitUnitary.rankStatement` gives `Nat.card I ≤ 1`.

The connected reductivity theorem supplies smoothness and affineness of
the unitary group. Base change from `F` to `E` preserves maximality.
Transport through `QuasiSplitUnitary.splittingIso` produces a maximal torus
of `GL₂` over `E`. Base change again to `K = AlgebraicClosure E` and
transport through `GeneralLinear.baseChangeIso` produce a maximal torus
of `GL₂` over `K`. Smoothness and connectedness of this group allow
`maximalTorusConjugacy` to compare it with the maximal diagonal torus.
Only the resulting isomorphism of commutative source group schemes is
needed; the conjugating point and conjugacy equation are discarded.

The private helper `toGrpIso` forgets commutativity on this source
isomorphism by applying `CommGroupScheme.groupHom` to its maps and
`congrArg Additive.toMul` to its inverse identities. Combining it with
the two split-torus base-change isomorphisms and the original splitting
of `T` gives an isomorphism
`splitTorus (Spec K) I ≅ splitTorus (Spec K) (ULift.{u} (Fin 2))`.
The index cardinality theorem for split tori therefore gives
`Nat.card I = 2`, contradicting the earlier bound. `simp` computes the
cardinality of the lifted two-element type, and `omega` closes the
arithmetic contradiction.

## Published inputs

Every directly invoked project theorem, and the project constructions
used to transport the tori, are listed here. Names below are in the
namespace `Langlands.GroupScheme`.

| Declaration | Module | Use |
| --- | --- | --- |
| `QuasiSplitUnitary.rankStatement` | `Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof` | Bounds the rank of the assumed closed split torus by one. |
| `IsClosedSubgroup.iso_comp` | `Langlands.GroupScheme.Rational.SplitTorus` | Preserves closedness on replacing the source by the split torus. |
| `QuasiSplitUnitary.isConnectedReductive` | `Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof` | Supplies smoothness and affineness before the first base change. |
| `maximalTorusBaseChange` | `Langlands.GroupScheme.Torus.MaximalBaseChangeProof` | Preserves maximality from `F` to `E` and from `E` to `K`. |
| `IsMaximalTorus.comp_iso` | `Langlands.GroupScheme.Torus.MaximalTransport` | Transports maximality along both ambient isomorphisms. |
| `QuasiSplitUnitary.splittingIso` | `Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting` | Identifies the unitary group over `E` with `GL₂`. |
| `GeneralLinear.smoothStatement` | `Langlands.GroupScheme.GeneralLinearSmoothProof` | Supplies smoothness of `GL₂` over `E` and `K`. |
| `GeneralLinear.baseChangeIso` | `Langlands.GroupScheme.Reductive.GeneralLinear` | Identifies the base change of `GL₂` with `GL₂` over `K`. |
| `connectedSpace_generalLinear` | `Langlands.GroupScheme.Reductive.GeneralLinear` | Supplies connectedness of `GL₂` over `K`. |
| `maximalTorusConjugacy` | `Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof` | Gives an isomorphism with the source of the diagonal maximal torus over `K`. |
| `GeneralLinear.isMaximalTorus_diagonalTorus` | `Langlands.GroupScheme.Reductive.GeneralLinearMaximal` | Certifies maximality of the diagonal torus of rank two. |
| `splitTorus.baseChangeIso` | `Langlands.GroupScheme.Torus.Split` | Identifies each base change of the split source with the same-index split torus. |
| `splitTorus.card_eq_card_of_iso` | `Langlands.GroupScheme.Rational.SplitRankTransport` | Equates the index cardinalities of isomorphic finite split tori. |

The proof also uses the published base-change functor `GroupScheme.baseChange`,
the forgetful map `CommGroupScheme.groupHom`, and the standard instances
for algebraic closures and affine general linear groups available through
the imports. Category-theoretic isomorphism composition and `mapIso`
assemble the displayed isomorphism. The statement pair and its entire
import closure are unchanged.
