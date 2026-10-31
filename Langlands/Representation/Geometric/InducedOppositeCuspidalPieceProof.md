# Cuspidal geometric pieces of opposite Jacquet modules of GL induction

Authors: Workers 164 and 954.

`Langlands.glInducedOppositeJacquetCuspidalPiece.{uF,uV,uW}` proves exactly
the published proposition
`Langlands.GLInducedOppositeJacquetCuspidalPieceStatement.{uF,uV,uW}`.
The field universe `uF`, the cuspidal target carrier universe `uV`, and the
inducing carrier universe `uW` remain independent.

For every prime, actual finite p-adic extension with supplied compatible
topological data, positive rank, and two block shapes `B` and `C`, the theorem
applies to every smooth representation `π` of the Levi of `B`. If an
irreducible cuspidal representation `ρ` of the Levi of `C` is an actual
subquotient of the opposite normalized Jacquet module of the normalized
induction of `π`, it gives a refinement `S` of `B`, a permutation `w`
conjugating the embedded Levi of `B.flatten S` onto that of `C`, and an actual
subrepresentation of the flattened upper normalized refined Jacquet module
of `π` whose inverse-conjugation transport surjects onto `ρ`.

The proof applies
`InducedOppositeCuspidalPiece.glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma`
from the paired helper module `InducedOppositeCuspidalPieceConditional` to
the published theorem `Geometric.padicGeometricLemma.{uF,uW}`. Thus the
geometric lemma is proved internally by the imported Library theorem. The
complete type has no additional premise, supplied filtration, or certificate.

The helper implements the following deduction.

1. Block reversal identifies the opposite Jacquet module along `C` with the
   upper one along `C.reverse`, after relabelling the target Levi. This
   relabelling preserves irreducibility and quasicuspidality.
2. The geometric lemma provides a finite natural filtration with actual
   geometric graded pieces. The irreducible actual subquotient occurs in
   one such piece, by `WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece`.
3. `CuspidalSupport.padicProperRefinedInduction` excludes every piece whose
   target refinement is proper. To apply that theorem without relating `uV`
   and `uW`, the reused proper-induction helper forms the quotient by the kernel of the given
   surjection inside the induced carrier universe `max uF uW`, then transfers
   quasicuspidality through its representation equivalence with `ρ`.
4. For the remaining whole-target piece,
   `Geometric.wholeLeviGeometricPieceEquiv` identifies it with the actual
   transport of the flattened upper refined Jacquet module of `π`.
5. Undoing block reversal composes the selected permutation with
   `C.reversePermutation`. Pulling an invariant subspace back through the
   Levi isomorphism produces the required subrepresentation and surjection.

The helper's paired Markdown details its implemented lemmas and the precise
transport directions. Worker 954 supplied that proof and its shared draft;
Worker 164 checked it against the current Library and supplied this
unconditional closing specialization. All pre-existing Library Lean files,
including the target statement and its imports, are unchanged. The conditional
helper's Markdown updates attribution and identifies this closing proof; its
implementation retains the published `GeometricExcessBranch` helper reuse.

This is a derived consequence of the published geometric lemma and
proper-induction vanishing, together with the concrete GL block-reversal and
whole-Levi transport constructions. The original representation-theoretic
source is Bernstein and Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 2.12 (printed p.448) gives the geometric lemma; section 2.4(a),(d)
(printed pp.446–447) gives the absence of nonzero quasicuspidal subquotients
of proper induction; section 1.7 (printed p.443) fixes inverse-isomorphism
transport. The combination proved here is not a numbered result of that
source.

The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
It retains the statement's hypotheses and conclusion, with no further
condition on `π` and no minimality, identity-piece exclusion, or numerical
claim about `w`.
