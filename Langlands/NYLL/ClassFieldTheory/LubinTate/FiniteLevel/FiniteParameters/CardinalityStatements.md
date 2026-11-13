# Finite unit parameter cardinality target (M358.008)

`Langlands.NYLL.LubinTate.standardLubinTateUnitParameter_natCardStatement`
is a Prop-valued definition with independent universes `u v`, implicit
`{K : Type u} [Field K]`, explicit `F : LocalField.{u,v} K` and `n : ℕ`.
It asserts that the natural cardinality of the actual quotient of
valuation-ring units by `higherPrincipalUnitGroup F.toCompleteDVF (n+1)`
is `(Nat.card F.residueField - 1) * Nat.card F.residueField ^ n`.
The quotient and canonical shared LocalField package come from the published
Definitions module. No field, valuation, uniformizer or quotient choice is added.

The exact source proposition is preserved without a finite-quotient hypothesis.
This pair proves no cardinality formula and installs no finiteness instance.
A separately accepted exact proof remains required. The source M359.030
Galois-cardinality proof, at LevelAutomorphisms.lean:611–612, uses M358.008 to
compare the unit parameter count with the degree of the standard level field;
this supplies its prerequisite role in Task 5888.

## Original source and modifications

Naganori Yamaguchi, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`:
M358.008 type lines 116–121 and proof lines 121–167. Source file SHA-256:
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
Registered snapshot `external-lean-reuse-snapshots-2026-10-21` has content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Changes: prefix the source namespace with `Langlands.NYLL`, extract this unit
into a focused module importing only the published unit parameter Definitions,
and replace the theorem by a definition returning Prop with `Statement`
appended. The full source telescope, quotient level, natural-cardinality
convention and formula are unchanged. The source proof and instances are
omitted here. The source header retains its copyright and attribution;
Apache-2.0 licensing and attribution are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` with supplement
`nyll-classfieldtheory-fbd320cd-supplement`.
