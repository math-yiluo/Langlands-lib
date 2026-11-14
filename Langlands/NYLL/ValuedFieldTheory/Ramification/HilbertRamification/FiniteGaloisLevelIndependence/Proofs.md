# Valuation-ring independence of the ramification filtration

Proof implementation for the five closed proposition targets in
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence.Statements`.
Their namespace is
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`;
each theorem name removes the target's `Statement` suffix. All retain the exact
independent universes, supplied extensions and target-specific uniqueness
hypotheses of their target. The last three also retain finite dimensionality.
The selected exact proof is
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.upperRamificationGroup_eq_of_valuationSubring_eq`,
whose type is the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.upperRamificationGroup_eq_of_valuationSubring_eqStatement`.
Its five independent universe levels correspond to the base field, its value
group, the extension field and the two target value groups. It retains both
`HasExtension` instances and both uniqueness predicates at their respective
target universes. It compares the actual subgroups of `Gal(L/K)` at every real
index; no completeness or Galois assumption is added.

The lower-group proof uses the identity-on-elements ring equivalence between the
equal valuation subrings. Mathlib `IsLocalRing.map_ringEquiv_maximalIdeal`, with
`Ideal.map_pow`, transports each real ramification ideal. The ring equivalence
commutes with the induced valuation-subring automorphism since both sides have
the same underlying field element. The lower-group membership characterizations
then give equality, transporting ideal membership in both directions.
This replaces the source's local-hom maximal-ideal argument with named existing
Mathlib reuse and requires no M317 port.
The membership transport uses Mathlib `Ideal.mem_map_of_mem` and
`Ideal.mem_map_iff_of_surjective`. The Library inputs
`valuationSubringAutOfUniqueExtension`, `realRamificationIdeal` and
`mem_lowerRamificationGroup_iff` in the same `Higher` namespace supply the
actual action, ideal and lower-group criterion.

The integral lower-filtration proof applies a private extensionality helper,
proved by destructing the filtration structures, to the natural-index lower-group
equalities. Forward and inverse Herbrand-function equality follow by congruence
on that filtration equality. Finally, unfolding the actual upper group as the
lower group at the inverse-Herbrand index gives upper-group equality.
Only published generic Herbrand and real-lower definitions/laws are imported;
the chosen finite-Galois-level constructions of M306 are not used.
In particular, the statement module imports the existing
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions`,
which supplies `herbrandFunctionOfUniqueExtension`,
`inverseHerbrandFunctionOfUniqueExtension` and
`upperRamificationGroupOfUniqueExtension`. The first two are the generic
`AntitoneNormalSubgroupFiltration` constructions on
`lowerRamificationFiltrationOfUniqueExtension`; the last is the actual lower
group at the inverse-Herbrand index. These published constructions replace the
source's broad `FiniteGaloisLevel` import. The only additional direct import is
Mathlib `RingTheory.LocalRing.RingHom.Basic`.

Pinned NYLL source commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteGaloisLevelIndependence.lean`:
M307.002 lines 50–147; .003 lines 151–163; .004 lines 168–184;
.005 lines 188–204; .006 lines 208–228; source extensionality helper lines 37–46.
Registered source `external-lean-reuse-snapshots-2026-10-21`.
Its registered content fingerprint is
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the original Lean file has SHA-256
`67f3ed98315313d33a9588b38e274e5ea310886ea00cda103b51a489775393a2`.
Modifications: focused extraction/imports, namespace prefix, closed-target theorem
interfaces and direct Mathlib ideal-transport reuse. No new global instance is
introduced. Original copyright and author notice and Apache-2.0 attribution are
retained; see `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 333 reuses Worker 296's implementation from the parent task's shared
draft revision 3, with the four preceding proofs as supporting lemmas. Worker
333 expanded this proof documentation; the Lean implementation is unchanged
from that draft. The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Independent proof review and
integration are required for publication.
