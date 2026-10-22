# Schreier factors and the actual group transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This internal bridge identifies Mathlib's `MonoidHom.transfer` with the
product of the subgroup factors
`q.out⁻¹ * g * (g⁻¹ • q).out`. The proof chooses the actual quotient
representatives as a left transversal and applies the proved
`MonoidHom.transfer_def` formula. Equality of subgroup elements is checked
on their underlying group elements.

The resulting additive formula is for the existing `abelianizationTransfer`,
which descends Mathlib's group transfer to the actual abelianization.
The final lemma identifies the dimension-one tuple in the independently
constructed ordinary homological transfer with these same Schreier factors.
Thus this bridge fixes both the transfer direction and the representative
convention needed in the degree-minus-two comparison.

Provenance is internal to the pinned Mathlib definitions and proofs in
`Mathlib.GroupTheory.Transfer` and `Mathlib.GroupTheory.Complement`,
commit `5ed2965256430c3649e86755f9576b54eca72435`, together with the explicit
chain formulas of this development. It expresses the transfer convention
of Serre, *Local Fields*, Greenberg translation, GTM 67 (1979), Chapter VII
section 7, printed pages 118–119 (PDF pages 124–125).
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre VII §8, Proposition 7, printed pp. 120–121 (PDF pp. 126–127),
is the specific source for the transfer on abelianizations. Serre uses right
coset representatives; taking the inverses of the chosen left representatives
gives the factors used here. The comparison with Mathlib's transfer is proved
directly by `groupTransfer_schreier`, so this change of convention is checked
in Lean.
