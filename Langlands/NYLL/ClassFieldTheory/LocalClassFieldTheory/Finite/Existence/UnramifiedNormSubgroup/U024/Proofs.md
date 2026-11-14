# Cardinality of the unramified valuation quotient

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degree`
proves exactly the published proposition
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degreeStatement`.
For every nonarchimedean local field `K : Type u` with the original
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances, and every natural `n` with
`[NeZero n]`, the conclusion is
`Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n`.
The subgroup is the published subgroup of actual field units whose normalized
integer valuation is divisible by `n`.

The theorem's declared type is the named closed proposition at universe `u`.
The proof introduces its original telescope and implements the source
cardinality calculation:

1. Apply `Nat.card_congr` to the underlying equivalence of the published
   `unramifiedNormQuotientEquivZMod K n`, identifying the quotient's natural
   cardinality with that of `Multiplicative (ZMod n)`.
2. Apply `Nat.card_congr Multiplicative.toAdd` to remove the multiplicative
   type tag.
3. Apply Mathlib's `Nat.card_zmod n`.

The proof imports the exact target, the published M266.020 equivalence
definition and Mathlib's cardinality support by Lean module name. It needs no
additional quotient equivalence hypothesis, chosen finite enumeration or global
quotient finiteness instance. The target, subgroup and imported data are
unchanged, including the source's nonzero-degree hypothesis. This result
computes the cardinality of the valuation-divisibility quotient; identification
with the norm subgroup of a field extension is a separate result.

## Source correspondence and modifications

This is M266.024, theorem
`LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degree`, lines 244–253 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The complete original
file was read and its SHA-256 verified as
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable errata entry was found in the project notes.

Worker 205 adapted the namespace and imports and expressed the theorem's type
as the published closed proposition, introducing its telescope before the
unchanged source calculation. Worker 563 reused Worker 205's shared draft
revision 1 for Task 6176 (`89584dbe-a880-4a96-be17-74c5eb6d00f4`),
checked the source correspondence and revised this explanation.
Worker 205 is credited as a coauthor of the contribution.
The original copyright, author and Apache-2.0 header are retained, with
modification records for both workers. The license and notices are published at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Development validation

Lean-service check `44224929-aa9c-4e3f-a9ec-ef5928f9fb2e` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module against Library
base `9d71020c4b80abb41dbf8102ded7d93202edf495` with zero errors and warnings.
Inspection of the named theorem retained universe parameter `u` and reported
only `propext`, `Classical.choice` and `Quot.sound`.
This development check is separate from independent proof acceptance and
candidate exact-target validation.
