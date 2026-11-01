# Relative Hom comparison from whole-induction isolation

Authors: Worker 526, with the central-block design of Worker 430, scalar
and source-twist guidance of Worker 359, literal shape transport of Worker
435 and Hom transport of Workers 845, 526 and 435. The namespace is
`Langlands.RelativeCosocleHomIsolationReduction`. Imported public results
retain their documented provenance.

`fineTwistHomEquiv` constructs a complex linear equivalence between the
fine Hom into the refined opposite Jacquet module of the coarse input
and its counterpart after the common coarse twist. Public refined
second adjointness first converts to maps from inner induction. The
common-character twist equivalence on intertwiners and precomposition
with the inverse `coarseTwistEquiv` convert to the inner induction at the
new parameter. The same public adjunction converts back. Fine-twist
regularity and relative admissibility establish every admissibility
condition. No chosen adjunction equivalence is an input.

`TemperedInductionFiniteGenerationInput` names finite generation over
the ambient group algebra of each actual normalized induction of a
real-twisted irreducible tempered coarse input at positive rank. It
retains independent field and coarse-carrier universes and the original
strict-order hypothesis.

`temperedInductionFiniteGeneration` proves this family. Character twisting
preserves irreducibility and admissibility. The twisted Levi module is
simple, hence Noetherian and Artinian and therefore of finite length.
The public `Classification.normalizedInductionFiniteLength`, due to
Worker 325, gives finite length of its actual normalized induction.
Its Noetherian consequence gives finite generation over the ambient
group algebra. An explicit definitional conversion identifies this
module with the bundled induced carrier. Temperedness is used here for
admissibility; strict order is retained but unnecessary for this step.

`upperBoundOfIsolationAndFiniteGeneration` assumes the entire public
`WholeInductionLeadingRealBlockStatement` and that finite-generation
family. It retains the exact parent telescope, including the nested
refinements, actual middle quotient and all five carrier universes.
No additional use of the middle representation is needed in this upper
bound.

The whole-induction maps feed
`ActualQuotientRealBlock.quotientRetractionOfFiniteGeneration`. It
constructs an actual coarse map `rQ` from the standard opposite Jacquet
module of the specified outer quotient to the twisted coarse input.
The actual opposite map of the outer surjection, composed with the
whole-induction embedding, gives the map back. Their composite fixes
the quotient's selected full-central real block at `size * t`.

`FineHomRealBlockFactorization.nestedFineHomPostcomposeInjective` then
makes postcomposition by the refined opposite Jacquet map of `rQ`
injective on the entire fine Hom space. The nested scalar calculation
supplies its source-block hypothesis, and public opposite admissibility
supplies its target admissibility. The inverse public opposite-refinement
transitivity equivalence transfers the parent's composed-opposite Hom
into the iterated fine Hom used by this injection. Its source remains
the actual opposite Jacquet module of the outer quotient itself.

The target Hom is finite dimensional by the public fine
opposite-Jacquet Hom finiteness theorem. The resulting linear injection
gives `finrank Hout` at most the finrank of the twisted coarse fine Hom.
`fineTwistHomEquiv` identifies that latter finrank with `finrank Hin`,
proving the upper inequality.

`comparisonOfIsolationAndFiniteGeneration` combines this upper bound
with `RelativeCosocleHomUpperReduction.comparisonOfUpperBound`.
Both finite-dimensionality conclusions and the reverse inequality come
from the public lower bound. All real-block operations retain uniform
generalized nilpotents; no Jordan–Holder count or semisimplicity argument
is used. The final entry supplies the whole-induction isolation hypothesis
and the finite-generation theorem just proved here.
