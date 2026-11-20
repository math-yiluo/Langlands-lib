# Proper cutoff under actual Weyl transport

`WeylTransports.parabolic_eq_top_iff` applies the structural split comparison
to the literal Levi conjugacy carried by an actual full-index Weyl
transport. `Associated.isProper_iff` then gives the same proper status
throughout each actual association class. The structural premise follows
from fixed-torus dynamic coverage by
`semistandardProperSplitComparison_of_dynamicCoverage`.

`ProperPartTransportStatement` concerns a pair of associated full indices.
Two linear evaluations in a common coefficient fiber agree after cutting off
the group part whenever they agree before the cutoff. The Lean proof keeps
both sides on a proper pair and sends both sides to zero on a group pair.
For the invariant lift in VIII.2 the evaluations are the representative
evaluation and the representative evaluation followed by the normalized
comparison. VII.1.4 supplies the original equality.

This is an algebraic step in applying VII.1.4 to the proper part. It uses
the full semistandard indices, including the actual Weyl and orbit
transport. The field, carrier and common evaluation space have independent
universes.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), VI.3, VII.1.4, VII.2.4, and VIII.2 on printed p. 321.
[DOI](https://doi.org/10.1017/S1474748003000082)
