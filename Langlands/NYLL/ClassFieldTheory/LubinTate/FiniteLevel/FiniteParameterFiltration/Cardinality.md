# Cardinality of the finite parameter subgroup

This proof targets exactly
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterSubgroup_natCardStatement`.
The independent universes `u, v`, field instance, explicit shared
`F : LocalField.{u,v} K`, implicit valuation-ring uniformizer `π`, its
explicit uniformizer proof, naturals `n, k`, and the ordered bounds
`1 ≤ k` and `k ≤ n + 1` are retained. The conclusion is the cardinality
of the actual image of the `k`th higher principal units in the quotient
by the `(n + 1)`st higher principal units:
`Nat.card F.residueField ^ (n + 1 - k)`.

Let `q` be the residue-field cardinality and let `H` be that image.
The inclusion `U^(n+1) ≤ U^k` follows directly from Mathlib's
`Ideal.pow_le_pow_right`. Mathlib's
`QuotientGroup.quotientQuotientEquivQuotient` identifies the quotient
of the level-`n` parameter group by `H` with the unit quotient by `U^k`.
The published theorem
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameter_natCard`
in `FiniteParameters.CardinalityProof` therefore gives
`H.index = (q - 1) * q^(k - 1)`, and gives `(q - 1) * q^n`
for the cardinality of the ambient parameter group.
Mathlib's `Subgroup.card_mul_index` now determines `Nat.card H`.
The finite residue field is nontrivial, so `q > 1`; cancellation
of the positive index and the natural-exponent identity
`(n + 1 - k) + (k - 1) = n` prove the stated formula.
The proof also covers `k = n + 1`.

The original is Naganori Yamaguchi's NYLL M363.003,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean:62–110`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`,
registered as `nyll-classfieldtheory-fbd320cd-supplement` (the Lean file
itself is in the snapshot `external-lean-reuse-snapshots-2026-10-21`,
folder `n-yamaguchi-0729--ClassFieldTheory/source/`, which that
supplement extends).
The source file SHA-256 is
`0205d0dc5727b940c1ca25159ddc4ba008423ec44a19e8d7ae024a8a9f6e1aa1`.
Modifications are the `Langlands.NYLL` namespace prefix, imports of the
unchanged public target and public full-parameter cardinality proof,
the exact-target packaging, and replacement of the source product
of graded-piece cardinalities by the argument described above.
The uniformizer hypothesis remains in the theorem telescope, although
this argument needs only the shared local-field structure.
The independent source universes and all hypotheses remain unchanged.
Original copyright, attribution and Apache-2.0 license pointers are retained.

This route uses no M120.051/.074/.083 or M231.018/.020/.023–026/.033/.063/.064
declaration and imports no private prerequisite copies.
