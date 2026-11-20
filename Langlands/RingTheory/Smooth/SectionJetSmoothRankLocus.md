# A closed smooth-section locus on a chart with conormal generators

Let `A` be a finitely presented commutative algebra over a noetherian ring `R`
with augmentation `ε`. Suppose `r` augmentation elements give generators of
its conormal module. `sectionJetSmoothRankLocus` characterizes the scalar
extensions `R → B` that kill the coefficient ideal of the polynomial jet maps.
They are exactly those for which the base-changed algebra is smooth at every
point of the section and its conormal has dimension `r` over every residue
field of `B`.

Scalar extension preserves the conormal generators and commutes with the
polynomial evaluation maps on the actual section jets. The conormal of a
zero-augmented polynomial algebra has the basis of variable classes, by the
identification with pulled-back Kähler differentials. Killing the coefficient
ideal gives a smooth neighborhood and makes the map on first jets bijective,
so the variable basis transfers to the test conormal. Conversely, smoothness
along the section makes the test conormal projective. A surjection from the
polynomial conormal is then bijective when both modules have rank `r` at the
stalks. The resulting basis makes all polynomial jet maps bijective.

This is the affine closed-chart part of Raynaud's SGA 3, Exposé XV, Lemma 5.4,
using full polynomial jet maps to impose his graded comparison conditions.
