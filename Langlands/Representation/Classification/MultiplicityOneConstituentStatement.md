# Multiplicity-one criteria for strong irreducible constituents

Authors: Workers 495 and 502. This is a derived internal algebraic interface.
It has no external source citation.

`MultiplicityOneConstituentCriterionStatement` is the conjunction of
`MultiplicityOneHeadCriterionStatement` and
`MultiplicityOneSocleCriterionStatement`. The source is the existing category
of smooth complex representations of an arbitrary group with a topology. The
target is the category of complex representations of an arbitrary monoid.
Group, monoid, source-carrier, image-carrier and test-carrier universes are
independent.

For the head criterion, the additive functor preserves epimorphisms. The
ambient functor image has Jordan–Hölder multiplicity one for a supplied test
representation. An actual smooth irreducible quotient exists, and every such
quotient has a positive test multiplicity in its functor image. Every
multiplicity premise retains an actual finite simple-series witness through
the existing `HasJordanHolderMultiplicity` relation. The conclusion is the
existing `HasIrreducibleHead` relation: every irreducible quotient map has the
same actual kernel. It is stronger than uniqueness of an isomorphism class.

The socle criterion replaces epimorphisms by monomorphisms and actual
quotients by actual embeddings. It concludes `HasIrreducibleSocle`, including
equality of the actual images of all irreducible embeddings.

The derivation rationale uses the published
`Classification.HeadQuotientCriterionProof` and
`Filtration.MultiplicityAdditivityProof` with its multiplicity transport
results. Unequal kernels of irreducible quotient maps give a surjection onto
their actual binary product. Smoothness transfers to each quotient, and the
product is smooth by intersecting the coordinate stabilizers. Images of the
four product inclusions and projections under an additive functor retain
their identity and zero composites. They provide the comparison with the
product of the two functor images. Epimorphism preservation, product
additivity and surjective monotonicity force the sum of the two positive
counts to be at most one, a contradiction. All quotient kernels must
therefore coincide.

Dually, the image of an injective irreducible intertwiner is an atom in the
actual subrepresentation lattice. Unequal atoms are disjoint, so the sum of
the two embeddings injects their actual product into the ambient
representation. Smoothness transfers to both sources. Monomorphism
preservation, the same split product comparison, product additivity and
injective monotonicity again bound two positive counts by one. All images
must therefore coincide. These arguments apply to isomorphic or identical
source or target representations; no inequivalence assumption is present.

The target imposes no finite dimension, admissibility, local compactness,
continuity of group operations, irreducibility of the test representation
or separate nonzero condition. Existence of one simple constituent and
positive detection of every simple constituent remain explicit hypotheses.
No result about a specific Jacquet functor, adjunction, parabolic induction
or segment constituent is included. The imports contain only the existing
generic representation categories, constituent relations and multiplicity
definitions, with no segment, multisegment, tempered or analytic
classification conclusion.
