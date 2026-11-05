# Full-centre containment from maximal-torus centralizers

This internal deduction proves
`NormalReductiveCenterCentralizerReductionStatement`: the existing
`AlgClosedMaximalTorusCentralizerStatement` implies the unchanged
`NormalReductiveCenterStatement`, in every universe. The former is an explicit
premise throughout. This module does not prove either structural proposition
unconditionally.

Over an algebraically closed field, the proved `maximalTorusExistence` chooses a
closed maximal torus of the connected reductive subgroup H. The proved
`torusFiniteGaloisSplitting`, followed by splitting reflection over an
algebraically closed field, makes that torus split. Every point of the full
centre of H commutes with all points of this torus after every refinement.
The assumed self-centralizer equality therefore places the full centre in the
torus as an inclusion of subgroup functors.

The proved full-centre representability theorem supplies a closed representative
Z of the centre of H. Its inclusion factors through the chosen torus, and that
factor is a closed immersion because its composite and the torus inclusion are
closed immersions. The theorem
`center_le_comap_of_normal_of_center_split_embedding` applies: ambient conjugation
restricts to an actual automorphic action on Z, and the proved rigidity of closed
subgroups of split tori under smooth connected affine group actions makes this
action trivial. Thus the full centre of H maps into the full centre of G over
the algebraically closed field. No smoothness or reducedness of Z is used.

For an arbitrary ground field, the proof first passes to its algebraic closure.
Connected reductivity, the closed immersion, and normality are preserved by this
base change. The maximal torus is chosen only over the algebraic closure, so the
argument requires no assertion about geometric maximality of a torus chosen
over the original field. The proved
`center_le_comap_of_baseChange_le` descends the resulting containment along this
fpqc field extension, using a closed representative of the ambient full centre.
Its comparison uses the full centre's compatibility with base change. The
conclusion consequently quantifies over every field and every test scheme,
including nonreduced tests, with all refinements retained.

The last theorem specializes this implication to the stronger, full-field
`MaximalTorusCentralizerStatement`.

The mathematical route is derived from Conrad, Gabber and Prasad,
*Pseudo-reductive Groups*, second edition (2015), Proposition A.1.13, printed
p.471 (PDF p.497, zero-based index 496), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
For the connected subgroup H considered here, the source's maximal torus of its
identity component is simply a maximal torus of H; self-centralization puts its
centre directly in this torus. The source uses multiplicative type and an étale
automorphism functor for rigidity. This Lean deduction instead reuses the
published all-test rigidity theorem for a closed subgroup of a split torus and
the published fpqc descent theorem. These are internal consequences of the
stated premise and existing proved interfaces, rather than an unconditional
formalization of Proposition A.1.13.
