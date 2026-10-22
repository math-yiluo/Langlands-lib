# Degree-minus-two restriction and abelianization transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The target `integralMinusTwoEquiv_restriction` identifies the constructed
restriction on actual Tate cohomology in degree minus two, for the trivial
lifted integral module, with Mathlib's actual group-theoretic transfer on
abelianizations. The equivalence used is the existing `integralMinusTwoEquiv`,
constructed from Mathlib's Tate-to-homology comparison and its first-homology
theorem for trivial coefficients, followed by the explicit lifted-integer
tensor equivalence.

The proof first evaluates the independently constructed ordinary transfer on
first-homology generators. Its chain formula yields the sum of the Schreier
factors. A generic representative lemma proves the action of an actual chain
map on Mathlib's `H1π`; no new first-homology groups are introduced.
The negative-degree transfer comparison then gives the corresponding formula
for `minusTwoClass`. Finally every integral degree-minus-two class has a
single representative with coefficient one, and the Schreier formula for
Mathlib's `MonoidHom.transfer` identifies its image under the abelianization
equivalence.

The theorem retains arbitrary carrier universe `u` and uses the actual
trivial coefficient module over `ULift.{u} ℤ`. No conclusion or transfer
operation is supplied as an assumption.

This is an internal proof of the classical low-degree transfer identification,
using the pinned Mathlib modules for group homology in low degree and group
transfer. Its source convention is Serre, *Local Fields*, Greenberg translation,
GTM 67 (1979), Chapter VII section 7, printed pages 118–119 (PDF pages 124–125),
and Chapter VIII sections 1–2, printed pages 127–130 (PDF pages 133–136).
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre VII §8, Proposition 7, printed pp. 120–121 (PDF pp. 126–127),
is the specific source for the transfer on abelianizations. Serre uses right
coset representatives; taking the inverses of the chosen left representatives
gives the factors used here. The comparison with Mathlib's transfer is proved
directly by `groupTransfer_schreier`, so this change of convention is checked
in Lean.
