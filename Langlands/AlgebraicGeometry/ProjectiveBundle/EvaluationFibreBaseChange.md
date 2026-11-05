# Actual evaluation sections through canonical direct-image base change

This internal derived construction uses schemes in one arbitrary universe,
a morphism `p : X ⟶ S`, a line bundle `L` on `X`, a module sheaf `M`
on `S`, and an actual evaluation morphism `ev : M ⟶ p_*L`. It compares
local coefficient sections with evaluation after a commutative square
`q ≫ p = p' ≫ g`. The square need not be Cartesian. Invertibility of
the canonical direct-image comparison is not assumed.

For an open `U` of `S`, an open `V` of the changed base with
`V ≤ g ⁻¹ᵁ U`, and a section `σ` of `M` over `U`,
`baseChangeEvaluation_sectionPullbackLE` proves that the canonical
changed evaluation of the restricted pullback of `σ` equals the
restricted pullback along `q` of `ev(σ)`. Both sides are sections over
`p' ⁻¹ᵁ V`. The source-open containment follows from the commutative
square. The proof applies the published `baseChangeEvaluation_adjunct`
identity to the pulled-back coefficient section, then uses the section
formulas for pullback composition, equality of morphisms and naturality.
The final adjunction section formula identifies the resulting section
with the canonical changed evaluation.

Fix a frame open `U : FrameOpen M n`, a point `s` in that open, and the
original residue spectrum `Spec (S.residueField s)`. Its map to `S` has
image `{s}`, so the entire residue spectrum maps into `U`.
`fibreFrameSections` is the family of actual frame coefficient sections
pulled back to this spectrum. `fibreFrameEvaluation` applies the canonical
changed evaluation, formed using the actual source fibre and its two
projections, to these coefficient sections. These definitions need the
specified frame, but no global fixed-rank or generation premise.

`fibreEvaluationLineIso` compares the two-step pullback of `L` through
the inverse-image frame open with the single pullback along the actual
fibre inclusion. It uses the published source lift's factorization and
the canonical composition and equality comparisons for module pullback.
A private general section lemma verifies that this comparison carries
two-step section pullback to single section pullback.
`fibreEvaluationLineIso_hom_sections` combines that lemma with the general
changed-evaluation formula: it carries each previously constructed
`fibreEvaluationSections` entry to the corresponding
`fibreFrameEvaluation` entry.

Under the explicit hypothesis `FrameEvaluationGenerates p L ev n`,
`fibreFrameEvaluation_generate` transports generation through this line
bundle isomorphism. `fibreFrameEvaluation_coordinates` then proves that
the relative linear-system map of these canonical changed evaluation
sections equals the previously constructed `fibreEvaluationCoordinates`,
over the original residue spectrum. The proof uses invariance of the
relative linear-system map under a line bundle isomorphism and the
entrywise section comparison. Thus the existing comparison of those
coordinates with the canonical whole-fibre map also applies whenever
its separate fixed-rank hypothesis is supplied.

The provenance is internal: the construction derives these comparisons
from the implemented evaluation-adjunction identity, section pullback
coherence, actual source-fibre lift, and invariance under line bundle
isomorphism. It does not assert that the pulled-back coefficients form
a basis of the full changed direct image. Cubic rank, invertibility of
direct-image base change, generation from abelian geometry, fibre very
ampleness, and representability remain separate obligations.
