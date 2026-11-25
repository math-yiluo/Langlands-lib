# Exactness target for free sheaf Čech nerves

This is an internal prerequisite statement for the
presheaf Čech construction, rather than a transcription of a literature claim.
It has no proof in this module.

`FreeCechCoverExactnessStatement C J R` asserts that, for every locally
surjective arrow f of presheaves of sets on the site (C, J), the actual
augmentation `freeCechAugmentation J R f` is a quasi-isomorphism. Local
surjectivity means that each section of the target lifts after restriction
along a covering sieve. The ring R is commutative; its carrier and presheaf
values lie in `Type w`. The only sheafification hypothesis is
`HasSheafify J (ModuleCat.{w} R)`. There are no products, pullbacks, or
subcanonical hypotheses on C.

The augmentation has source the alternating face map chain complex of the
presheaf Čech nerve after applying free R-modules and sheafifying. Its target
is the chain complex concentrated in degree zero at the free sheaf on the
target presheaf. Thus the asserted quasi-isomorphism says that degree-zero
homology identifies with that free sheaf through the canonical augmentation,
and all positive homology vanishes.

This formulation uses the constructions in `FreeNerve`. In particular its
`familyArrow_isLocallySurjective_iff` identifies an ordinary covering family
with a locally surjective arrow from the coproduct of its representable
presheaves. The statement therefore includes covering families without
requiring fiber products in the geometric category.

The intended mathematical mechanism is local contraction of the augmented
nerve after choosing a lift of a section, followed by exact sheafification.
That is a proof obligation, not an assumption supplied by this statement.
Neither derived sheaf cohomology nor its comparison with Čech cohomology
appears here, and no acyclicity claim for restricted equivariant injectives
is asserted.
