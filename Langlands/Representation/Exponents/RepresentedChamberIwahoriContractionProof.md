# A chamber of Iwahori contractions for a represented parabolic

This module proves the exact published
`Langlands.Aubert.General.RepresentedParabolic.RepresentedChamberIwahoriContractionStatement`
at universe `u`, with theorem `representedChamberIwahoriContraction` in the same namespace.
The statement and its imports are unchanged.

The result is the derived chamber step used in Renard, *Représentations des groupes
réductifs p-adiques*, version of 9 July 2026, V.5.2 (iii)–(iv), printed p.123
(PDF p.129), and VI.6.1, printed pp.176–177 (PDF pp.182–183). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`.
The governing definitions, scope and source conventions are described in
`RepresentedCanonicalSectionStatements.md`.

## Implemented proof

The auxiliary theorem `eventually_pow_characterNorm_lt` uses convergence of powers
of a nonnegative real number less than one to zero. Finiteness of the character set
gives a common bound on the powers. Unlike the earlier `exists_pow_mem_CAepsilon`,
this lemma has no lattice-image hypothesis: the target concerns every point of
the split component.

The auxiliary theorem `represented_chamber_nonempty` takes a standard cocharacter
from the supplied root presentation and lifts it integrally through the split
component with `exists_standardCocharacter_lift`. Its pairings with the restricted
complementary simple roots are positive. Evaluating at a uniformizer therefore
gives all character norms less than one, by
`characterNorm_latticeSection_lt_one`. A sufficiently large power lies in any
prescribed positive chamber. These two auxiliary theorems are internal derived
lemmas, obtained from the published presentation and norm evaluation results.

For the main theorem, the intersections of the compact open subgroup `K` with
the two radical point images are compact because the radical images are closed.
The published `splitComponentOppositeContraction` applied to these intersections
and the neighbourhood `K` supplies a positive threshold. Shrink it to at most
one. The two containment conclusions, together with normalization of each
radical by the Levi, prove the upper and lower fields of
`Jacquet.IsIwahoriContraction`.

The image of the component point belongs to the Levi image and commutes with it,
by `splitComponent_point_comm`; this gives the membership and Levi fields.
The factor field is exactly the given ordered Iwahori decomposition.
For exhaustion, apply the same geometric contraction theorem to the singleton
of any radical point and use a high power of the given chamber point.
For uniform contraction of the opposite intersection into any open subgroup,
apply it to that compact intersection and the given open subgroup, and again
use a high power. The auxiliary convergence theorem applies because every
character norm is strictly less than the threshold, which is at most one.
This proves all seven fields for every point in the chosen chamber.

The proof adds no hypotheses on `K` beyond compact openness and its stated
Iwahori decomposition, and no restriction of the chamber to the lattice image.
