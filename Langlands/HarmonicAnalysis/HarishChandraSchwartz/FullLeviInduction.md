# Full-group normalized induction and coefficient transport

This derived auxiliary module supplies the representation part of the group-Levi
endpoint in the lower-inclusion argument of Waldspurger, *La formule de
Plancherel pour les groupes p-adiques*, VIII.4.2, printed p.330 (PDF p.96).
It uses the normalized induction conventions of I.3, printed p.243 (PDF p.9), and the tensor
coefficient map of V.1. It does not prove a wave-packet estimate, identify
Plancherel densities or orbit measures, or prove either closed VIII.4.2 target
(`RationalCuspidalDiscreteCoefficientStatement`, `RationalCuspidalFixedCoefficientLiftingStatement`).

For a locally compact nonarchimedean group, an actual semidirect decomposition
with full parabolic and Levi, a trivial radical supplied with a proof of
closedness, and a smooth complex Levi representation,
`fullLeviInductionEquiv` evaluates normalized induced functions at one.
Its inverse sends a vector to its orbit function. The target representation is
the original Levi representation pulled back through the literal continuous
group equivalence with the ambient group. It retains the original carrier
universe `uV`; the induced source has the usual carrier in `max uG uV`.

The proof first verifies that the actual Haar normalizer character, hence its
half-character, is one on a trivial radical. The normalizer conjugation is the
identity on the subsingleton subgroup, so its Haar multiplier is one. This is
the argument already used privately in the published Aubert endpoint module.
The semidirect projection is the identity on ambient elements because its
error lies in the trivial radical. The published full-subgroup smooth-induction
evaluation equivalence then gives the claimed representation equivalence.
The generic ambient assumptions do not impose Hausdorff separation, so
triviality of the radical does not itself discharge the closedness input.

`fullLeviInductionTensorEquiv` applies the published coefficient-tensor transport
to this equivalence. Its coefficient-map theorem is equality of the literal
locally constant functions on the ambient group. No scalar occurs in this
algebraic identity, and no measure is chosen or changed.

`rationalFullLeviInductionEquiv` specializes to all simple roots on actual
rational points. It uses the proved standard-cocharacter theorem and the
published full-index identities for the standard parabolic, Levi, and radical.
This rational-point specialization supplies the radical-closedness proof.
It keeps independent field and representation-carrier universes. The
coefficient comparison to a product-induced packet and the source orbit-measure
normalization are in `FullLeviProductCoefficients` and `FullLeviOrbitMeasure`.

The ambient action is the `SmoothRep.pullback` along `fullLeviGroupEquiv`.
