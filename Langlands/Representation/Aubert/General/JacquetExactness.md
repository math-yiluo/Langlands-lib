# Exactness transport and support reflection for the actual general complex

This is a derived, conditional helper for corrected Aubert Theorem 3.6.
It uses the actual normalized Jacquet comparison in
`General.JacquetCutDiagram`, the exactness predicate of
`General.StandardExactness`, and the proposition
`General.SupportCategoryExactnessDetectionTarget`. No original literature
assertion is added.

The finite root index `ι`, ambient group `G`, and input carrier use independent
universes `uI`, `uG`, and `uV`. The input is any smooth complex representation
with carrier in `Type (max uG uV)`. All semidirect, closedness, modulus and
monotonicity hypotheses are those of `General.JacquetCutDiagram`. No
finite-length, admissibility, nonempty-root or endpoint premise occurs.

`jacquetDegreeRepresentationEquiv` bundles `jacquetDegreeEquiv` with its
proved compatibility with the actual inverse-half-modulus normalized Levi
action. It is an equivariant linear equivalence from Jacquet of the actual
homogeneous object to the coordinatewise normalized Jacquet representation.

`jacquetDifferential_injective_iff` transports injectivity through the two
degree equivalences and their proved differential square.
`jacquetDifferential_exact_iff` transports equality of the incoming range and
outgoing kernel through the three consecutive degree equivalences. Its proof
uses Mathlib's
`LinearMap.exact_iff_of_surjective_of_bijective_of_injective` and
`LinearMap.exact_iff`. These arguments parallel the related GL-specific
`ActualCutComplex.jacquetDifferential_injective_iff` and
`ActualCutComplex.jacquetDifferential_exact_iff` in `Aubert.JacquetCutExactness`;
the present input objects and functors are those of the general subgroup
families. The existing general comparison supplies the commuting squares
with the literal exterior signs.

`isExactBeforeTerminal_of_jacquet` assumes all of the following:

- `SupportCategoryExactnessDetectionTarget` for the same families, closed
  Levis, Levi decompositions and association predicate;
- membership of every actual homogeneous object in `Alg({I})` in degrees
  strictly below `Complex.terminalDegree I`;
- injectivity at Jacquet degree zero along every standard Levi associated to
  `I`, when the terminal degree is positive;
- equality of the Jacquet differential range and next kernel at every
  positive degree strictly below the terminal degree, along each such Levi.

Every use of association carries both `IsAssociate I J n` and the actual
conjugation equation for `M I` and `M J`. The Jacquet hypotheses are required
at the original threshold `Complex.terminalDegree I`; no unproved equality
of the cardinalities of associated indices is used. Detection is explicitly
required at carrier universe `max uI uG uV`, the universe of the homogeneous
finite product. This preserves independent root and carrier universes.

The proof treats degree zero using the smooth sequence whose incoming arrow
is the zero endomorphism and whose outgoing arrow is the actual degree-zero
differential. The actual normalized Jacquet functor sends this zero arrow to
zero, as checked on quotient representatives. Jacquet injectivity therefore
gives exactness of each image sequence. Detection reflects this exactness,
which says that the degree-zero kernel is zero. At a positive degree, the
incoming and outgoing smooth arrows are the two consecutive actual degree
morphisms. The transport lemma and the assumed Jacquet range-kernel equality
give exactness of every image sequence. Detection reflects that equality to
the original smooth sequence. Unfolding the published boundary definition
gives exactly `StandardComplex.IsExactBeforeTerminal`.

This module does not prove support membership, exactness detection, associated
rank preservation or any Jacquet exactness premise. It contains no Bruhat or
graded-geometric comparison and proves neither the full rational target nor
vanishing of its retained terminal cokernel.
