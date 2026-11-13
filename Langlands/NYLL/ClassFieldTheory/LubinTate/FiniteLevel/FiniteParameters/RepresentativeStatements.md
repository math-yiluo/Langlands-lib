# Unit parameter representative targets (M358.006/.007)

The two proposition definitions in this pair preserve the full telescopes
and conclusions of the original representative and quotient-equality theorems.
Both use `{K : Type u} [Field K]`, explicit `F : LocalField.{u,v} K` and
`n : ℕ`, with the canonical shared LocalField and concrete higher-principal-unit
subgroup from the imported Definitions pair. Neither introduces an instance.

With prefix `Langlands.NYLL.LubinTate`,
`standardLubinTateUnitParameterChosenRepresentative_specStatement F n a`
states that the quotient class of the chosen unit representing
`a : standardLubinTateUnitParameter F n` is exactly `a`.
`standardLubinTateUnitParameterClass_eq_iff_div_memStatement F n a b`
states that the classes of the supplied valuation-ring units `a` and `b`
are equal if and only if `a/b` lies in `U^(n+1)`.
These are Prop-valued definitions. This pair supplies no proof or simp theorem.

## Original source and modifications

Naganori Yamaguchi, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`:
M358.006 type lines 88–92 and proof lines 93–95;
M358.007 type lines 99–105 and proof lines 106–112.
Source file SHA-256:
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
Registered snapshot `external-lean-reuse-snapshots-2026-10-21` has content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Changes: prefix the source namespace with `Langlands.NYLL`, replace each
theorem by a definition returning Prop with `Statement` appended to its name,
omit the source proofs and the source simp attribute on .006, and import the
focused unit parameter Definitions pair. Source universes, arguments,
explicitness, quotient level, subgroup and conclusions are unchanged. The
source header's copyright and attribution remain; Apache-2.0 licensing and
attribution are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
