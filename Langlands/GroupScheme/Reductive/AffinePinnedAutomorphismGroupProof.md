# Automorphisms of a pinned split reductive group over a connected affine base

`Langlands.GroupScheme.affinePinnedAutomorphismGroup` proves exactly
`AffinePinnedAutomorphismGroupStatement.{u}` in every universe, with no
additional hypotheses. It retains the statement's connected affine base,
supplied reductive group, coordinate split maximal torus, full fibrewise root
datum, free root spaces, base and pinning. It applies to every supplied fppf
quotient by the full centre and every supplied compatible conjugation action.

The proof applies
`affinePinnedAutomorphismGroup_of_localPinnedRepresentatives` to two
unconditional inputs from the Library:

1. `affinePinnedIsomorphismTheorem_of_unpinned
   affineSplitIsomorphismTheorem` supplies the exact affine pinned isomorphism
   statement. The unpinned theorem constructs an actual compatible group
   isomorphism; the pinned reduction corrects its simple-vector unit
   discrepancies and applies pinned uniqueness. Its full torus-character and
   chosen-vector equations give unique exact pinned representatives for based
   root-datum automorphisms, with the inverse label used to match the target's
   covariant convention.
2. `AffinePinnedModel.hasFppfLocalPinnedRepresentatives` supplies local pinned
   representatives for actual comparisons over arbitrary common schemes.
   The imported geometric reduction descends such a representative, extracts
   its single full root-datum label on the connected original base, and
   represents the inner discrepancy by a section of the supplied full-centre
   quotient. Relative pinned inner rigidity gives separation of the based
   label from that inner image.

The imported assembly uses these representatives, factorization and separation
to construct the projection from actual group automorphisms to full
root-datum automorphisms. Its kernel is precisely the image of the supplied
adjoint action, whose homomorphism is injective. The projection has exactly the
based automorphisms as image, and every based label has a unique exact pinned
representative on which the projection takes that label. These are all the
clauses of the unchanged target.

This is an internal composite proof of the published statement. The Lean file
imports its prerequisites by module name and changes neither the target's
Lean/Markdown pair nor any imported pair. The algebraic assembly is due to
Worker 588; Worker 237 supplied the geometric splitting used here.
