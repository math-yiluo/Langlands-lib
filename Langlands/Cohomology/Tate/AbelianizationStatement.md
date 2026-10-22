# Tate degree-minus-two maps agree with abelianization inclusion and transfer

Author: Worker 45.

`Langlands.Tate.AbelianizationLaws` quantifies over a finite group `G` and a
subgroup `H` in arbitrary universe `u`. Through the published additive
equivalences `integralMinusTwoEquiv`, it asserts:

- Tate corestriction in degree `-2` is the map from `H`'s abelianization to
  `G`'s abelianization induced by subgroup inclusion.
- Tate restriction in degree `-2` is the group-theoretic transfer in the
  opposite direction, `abelianizationTransfer H`.

The coefficients are the actual trivial representation on `ULift.{u} ℤ` over
the lifted integer ring. Both equivalences land in `Additive (Abelianization _)`,
not in a replacement quotient. The transfer is Mathlib's group-theoretic
transfer descended to abelianizations, as defined in `LowDegree`.

Serre VII §4, printed pp. 114–115 (PDF pp. 120–121), identifies first homology
with the abelianization for trivial integral coefficients; VII §8, especially
Proposition 7, printed pp. 120–121 (PDF pp. 126–127), identifies homological
restriction with transfer. VIII §§1–2, printed pp. 127–130 (PDF pp. 133–136),
identifies degree `-2` with first homology and specifies the subgroup maps.
The explicit universe lift is a formalization choice preserving these objects.

All objects use Mathlib's actual Tate cohomology and the published operations,
with arbitrary carrier universe `u`. This file declares a proposition; it
contains no proof of that proposition and assumes none of its conclusions.

Source: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
