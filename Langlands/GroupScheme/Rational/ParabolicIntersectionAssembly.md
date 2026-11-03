# Maximal split-torus conjugacy through a common torus

`ParabolicIntersectionSplitTorusStatement.{u}` asserts that any two actual
parabolic subgroups of a connected reductive group over a field contain
an ambient maximal split torus. Containment is expressed by actual
group-scheme factorizations of its inclusion through both parabolic
inclusions. All schemes and fields range over arbitrary universe `u`;
there are no restrictions on the field. The statement is defined here,
and is not proved unconditionally.

This interface is a derived weakening of Borel–Tits, *Groupes réductifs*
(1965), Corollary 4.18, printed p.92 (one-based PDF page 39). That
corollary places the centralizer of an ambient maximal split torus in the
intersection. The torus lies in its own centralizer, so the corollary also
gives the weaker containment expressed here. The existing
`ParabolicIntersectionCentralizerStatement` retains the stronger all-test
centralizer containment.

`parabolicIntersectionSplitTorusStatement_of_centralizer` proves this
weakening from the stronger statement as an explicit premise. It composes
`range_le_torusCentralizer` with each centralizer containment. Each
parabolic is closed and hence a monomorphism representing its own all-test
range. `SubgroupFunctor.IsRepresentedBy.factorHom` then constructs the
actual two group-scheme factorizations. This proof does not establish the
centralizer-containment premise.

`maximalSplitTorus_subgroupConjugate_of_parabolicIntersection` assumes the
common-torus statement, rational conjugacy inside a minimal parabolic of
ambient maximal split tori factoring through it, and minimal-parabolic
containment for the ambient maximal split tori. Choose minimal parabolics
containing the two supplied tori and obtain a common maximal split torus
from the intersection premise. Inside the first parabolic, conjugate the
first torus to the common torus; inside the second, conjugate the second
torus to the common torus. Postcomposition carries both conjugacies into
the ambient group. Symmetry and transitivity produce rational ambient
conjugacy with an actual source isomorphism.

`maximalSplitTorusConjugacyStatement_of_parabolicIntersection_extension`
adds explicit maximal extension of every closed finite split torus.
The preceding conjugacy result supplies the input to the published
split-rank reduction. It concludes the exact existing universe-general
`MaximalSplitTorusConjugacyStatement`, with both rational conjugacy and
equality of the finite splitting cardinal with `splitRank G`.

These last two proofs are internal categorical assembly. The
common-torus, inside-parabolic conjugacy, minimal-parabolic containment
and maximal-extension premises all remain explicit. The file does not
prove the unconditional host target.
