# Canonical reflexivity and admissibility

Worker 6 supplied the complete proof draft. Worker 1149 audited the governing
source, the exact published statement and the imported constructions, and added
this attribution and submission record.

This proof establishes
`NonUnitalModuleAdmissibilityStatements.AdmissibleIffEvaluationBijective`
over an original nondegenerate module for a possibly nonunital idempotented
complex algebra. Algebra and module carrier universes are independent.
The exact statement, fixed-bidual comparison proof and actual bidual injection
are imported unchanged from the published Library.

The source is Renard's French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.5.1 unnumbered proposition and proof, printed p.26 / PDF32.
The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2, corrects the converse argument on printed 2010 p.29 by passing
through the ordinary algebraic bidual of each fixed space. The 2026 proof
incorporates this correction and governs.

For the forward direction, the published separation theorem supplies
injectivity of the exact original-action evaluation. Every vector of the
actual nondegenerate bidual has an original fixing idempotent e. Admissibility
makes the canonically scalar-equipped fixed space finite-dimensional.
Mathlib's surjectivity of its canonical ordinary evaluation supplies a fixed
vector x representing the corresponding ordinary bidual functional. The published
comparison's left inverse and canonical evaluation square identify evaluation
of x.val with the original actual bidual vector.

For the converse, take an arbitrary ordinary bidual functional on the actual
e-fixed space. Send it into the actual e-fixed bidual and use surjectivity of
the original evaluation to obtain m. Injectivity and original A-linearity of
that same evaluation imply that e fixes m. The canonical evaluation square and
the comparison's right inverse identify the ordinary evaluation of this fixed
vector with the arbitrary functional. Thus ordinary canonical evaluation is
bijective, giving Mathlib's `Module.IsReflexive` for this fixed space.
Mathlib's `Module.instFiniteDimensionalOfIsReflexive` over the complex field
then proves finite-dimensionality for exactly its canonical coefficients.
No global finite-dimensionality of the original module is assumed or obtained.

The aggregate proof in `NonUnitalModuleAdmissibilityProof` combines this
canonical reflexivity criterion with dual admissibility and dual simplicity.
The proof adds no abstract bidual equivalence or algebraic reflexivity premise.
