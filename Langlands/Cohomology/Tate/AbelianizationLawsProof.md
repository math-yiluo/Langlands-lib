# Proof of the integral degree-minus-two subgroup laws

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

`Langlands.Tate.abelianizationLaws.{u}` has exactly the published type
`Langlands.Tate.AbelianizationLaws.{u}`. It quantifies over every finite group
`G : Type u` and subgroup `H` with the stated finite-type instances. The
coefficients are the actual trivial representation on `ULift.{u} ℤ`.
Under `integralMinusTwoEquiv`, corestriction in degree `-2` is
`abelianizationInclusion H`, and restriction in degree `-2` is
`abelianizationTransfer H`, defined using Mathlib's group transfer.

The proof first identifies the negative-degree Tate maps with ordinary
homology maps. `BoundaryDiagrams` and `SpliceRepresentatives` compute actual
connecting maps on cycle representatives. `CochainComparison` constructs
an auxiliary zero splice from the ordinary chain and cochain complexes;
`ChainComparison` maps the actual Tate complex to that auxiliary complex.
`NegativeCorestriction` and `NegativeRestriction` establish the norm-kernel
formulas in degree `-1`. `NegativeHomologyComparison` and
`NegativeTransferComparison` propagate these formulas to lower degrees,
using the actual coinduced augmentation sequence and injectivity of its
auxiliary connecting maps. The scalar splitting needed for Tate connecting
compatibility is constructed for that sequence; it is not an added
hypothesis of the final theorem.

`HomologyTransferRepresentatives` computes the independently constructed
ordinary transfer on chains, and `HomologyTransferNaturality` proves the
coefficient and connecting-map compatibilities needed in the induction.
`SchreierTransfer` identifies its degree-one factors with the factors in
Mathlib's group transfer. Finally, `AbelianizationCorestriction` and
`AbelianizationRestriction` compute both maps on `minusTwoClass` with
coefficient one. Every integral degree-minus-two class has such a
representative, by the surjectivity of the quotient map to the actual
abelianization and the proved formula for `integralMinusTwoEquiv`.
The entry theorem pairs the two resulting universal identities.

The target statement and its dependencies are imported unchanged. The
auxiliary zero splice is only a comparison complex: no Tate group or
subgroup operation in the target is replaced. The implementation retains
arbitrary universe `u` and assumes none of the compatibility conclusions.

This is an internal proof using the published constructions and pinned
Mathlib, commit `5ed2965256430c3649e86755f9576b54eca72435`. Its mathematical
sources are Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
VII §4, printed pp. 114–115 (PDF pp. 120–121), for first homology and
abelianization; VII §7, printed pp. 118–119 (PDF pp. 124–125), for subgroup
maps; VII §8, Proposition 7, printed pp. 120–121 (PDF pp. 126–127), for
transfer; and VIII §§1–2, printed pp. 127–130 (PDF pp. 133–136), for Tate
comparison and dimension shifting. Registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
