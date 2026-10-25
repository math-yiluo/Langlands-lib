# Conditional representation objects for gamma descent

This internal module packages actual positive-rank representations of full
Whittaker type over a fixed canonical p-adic field, in the carrier universe
`max uF u`, which is closed under the actual normalized induction. Each object
retains admissibility, finite generation over the group algebra, and the
one-dimensional entire functional space. Reducibility is unrestricted.

The ordered block family has indices `![a,b]`, and its total index is `b+1+a`.
The induced object uses the actual `canonicalNormalizedProductInduced` with
that family and `succBlockShape`. Its full type is supplied by an explicit
`NormalizedProductWhittakerTypeStatement` premise. Chosen gamma values are
units constructed by `padicSymmetricGammaFactorOfWhittakerType` from the
explicit `WhittakerTypeGammaConstructionInputStatement` premise. Their
certificates are retained. Symmetry follows from the explicit equal-rank
swap premise when the ranks agree, and from the published larger-rank-first
predicate when they differ, followed by uniqueness for the chosen units.

This is internal packaging for the two descending inductions of JPSS (1983),
section 7, printed 438–442. It discharges no analytic existence, symmetry, base
case, or type-preservation input. No source normalization comparison is
assumed: the induction and all premises use the published upper convention.
The actual lower-to-upper source reversal remains an obligation of the
separately owned analytic base proofs. This module is not the requested
closed multiplicativity theorem.

The representation instantiation converts each base statement's finite-product
certificates to equalities of chosen units, using uniqueness for each pair.
It then applies the separately implemented abstract two-stage descent.
`allRanks_eq` proves a conditional equality for all three positive ranks and
all ordered input objects, with a supplied rank-one object. The dominant,
adjacent, rank-one test, normalized-type, construction-input, and equal-rank
swap statements remain premises. None is claimed to be a published proof.

`certified` restores the target's arbitrary dependent two-block carrier
family. It first eliminates the rank-index function into its two values and
uses the given sum equality to identify the total rank. For each block it
constructs the identity representation equivalence from the internally
assembled ordered family to the original representation. The published
`normalizedProductInducedEquiv` applies these equivalences to the actual
normalized induction. Certificate transport then gives the original target
induced representation and the finite product of the two chosen witnesses.
This is a comparison of actual representation carriers and actions; it is
unrelated to the separately required source lower-to-upper reversal.

The structural match on `Fin 2` constructs the Type-valued block
equivalences; finite membership case elimination is used only for
proposition-valued goals. Lean's definitional equality identifies the
bundled induction with the actual induction on this ordered family, using
proof irrelevance for the rank-sum witness. The finite heartbeat bound on
`certified` permits this dependent elaboration.
