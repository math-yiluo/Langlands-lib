# Degree-minus-two corestriction is abelianization inclusion

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The theorem `integralMinusTwoEquiv_corestriction` identifies the constructed
Tate corestriction with the actual map on abelianizations induced by subgroup
inclusion. It uses the actual trivial coefficient representation over
`ULift.{u} ℤ` and the explicit lifted-integer equivalence from `LowDegree`.
The group carrier remains in arbitrary `Type u`.

The proof first applies the ordinary homology comparison, then Mathlib's
first-homology representative and functoriality results. A single chain
indexed by a subgroup element maps to the chain indexed by that element in
the full group. Mathlib's proved first-homology/abelianization theorem and
the integral tensor equivalence show that every class is represented by
such a single chain with coefficient one. This proves the formula for all
classes, not only for selected representatives.

Sources: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VIII, section 1,
printed pages 127–129 (PDF pages 133–135), together with Mathlib's
`groupHomology.H1AddEquivOfIsTrivial`, its single-chain formula, and
`groupHomology.H1π_comp_map`. The group-theoretic map is
`Abelianization.map H.subtype`, as in `LowDegree`. The separate identification
of restriction with group transfer is not asserted here.

Serre VII §4, printed pp. 114–115 (PDF pp. 120–121), gives the
first-homology identification with the abelianization. The integral tensor
transport and representative-surjectivity proof here are internal
formalization steps. Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
