# Actual induction adjunction interface checks

These internal checks accompany `NondegenerateInductionAdjunctionStatements`.
They assume and prove neither principal adjunction. Their provenance is internal
interface validation; the paired statement module gives the original sources
and the boundary of its arbitrary-ring additive formulation.

The checks give the complete unapplied signatures of both canonical predicates
and exact unfoldings of those predicates, both closed targets, and the shared
additive correspondence coherence. In particular these unfoldings expose the
existential actual adjunctions and additive Hom equivalences, whole inverse
quotient lifts and inverse identities, unit and counit formulas, whole-map
naturality in both directions, and both whole-morphism triangles.

The universe matrix uses arbitrary independent `uA`, `uB`, and `v` with common
carrier universe `max uB v`, followed by the assignments
`(uA,uB,v)=(0,1,0),(1,0,1),(1,0,0)`. The last makes the ring A universe
strictly larger than the carrier universe. Actual functor and composite types
are checked in every case. The arbitrary-universe checks also expose evaluation
through the original Hom subtype, the entire published inverse lift, object
carriers, group and action structures, and the fixed-factor tensor and
restricted-postcomposition morphism maps.

Each competing-instance section introduces other ring and additive-group
structures on the same carriers and other original module, tensor, ambient-Hom,
and Hom-part structures. Explicit original arguments check that the canonical
predicate remains well typed and the published F/I or P/pseudoF functors retain
the specified carrier, additive group, and action. The section variables are
written with expanded structure arguments, so no local notation hides their
dependencies. The two private subtype abbreviations select the existing
submodule instances before competitors enter scope; they define no new action.

The integer checks use exactly the left and right regular actions on Z,
their published commutation and nondegeneracy laws, and the corresponding
nondegenerate integer object. Both predicates specialize, both inverse maps
evaluate by the prescribed pairing, and the residual tensor action sends
`2 • (1 tensor n)` to `2 tensor n`. These are interface and definitional
checks, with no assumed adjunction.

The subsingleton checks allow B to be a zero ring, retaining either handed
family and the supplied A-action. They instantiate the predicates using
intrinsic subsingleton commutation and nondegeneracy and prove that the
corresponding actual Hom-part outputs are subsingletons by equality of
their underlying original maps. A final check bundles any subsingleton
original module as nondegenerate, using the zero idempotent.
No nonzero module with zero action is presented as nondegenerate.

These checks assign already implemented declarations, prove definitional
equalities, or use the published subsingleton laws. They are not separate
mathematical assertions attributed to Renard.
