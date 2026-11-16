# Natural degree of the standard Lubin–Tate polynomial (M339.006)

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_natDegreeStatement`
with the theorem
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_natDegree`.
Its declared type is the fully applied imported proposition
`standardLubinTatePolynomial_natDegreeStatement F π`.

The theorem preserves independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit arguments
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`
and `(π : F.valuationSubring)`. It states
`(standardLubinTatePolynomial F π).natDegree = Nat.card F.residueField`.
The element `π` is arbitrary; no uniformizer or extra finiteness hypothesis
is assumed.

## Implemented proof

Unfold the imported proposition and the published polynomial definition to
obtain the natural degree of `X ^ q + C π * X`, where
`q = Nat.card F.residueField`. Apply
`Polynomial.natDegree_add_eq_left_of_natDegree_lt`, which reduces the proof
to the degree of `X ^ q` and strict dominance over the second summand.

`Polynomial.natDegree_X_pow` gives the first degree as `q`.
For the strict inequality,
`Polynomial.natDegree_C_mul_X_pow_le π 1`, simplified by `pow_one`, bounds
the degree of `C π * X` by `1`, including when `π = 0`.
`Finite.one_lt_card` gives `1 < q`: the local-field package supplies the
`residueFinite` instance, and its residue field is nontrivial as a field.
Combining these inequalities completes the same argument as the original
source. No helper declaration or instance is introduced.

## Source and correspondence

The proof is adapted from M339.006, theorem
`LubinTate.standardLubinTatePolynomial_natDegree` at line 101 (type lines
100–104, proof lines 105–114) of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L100-L114),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The file header, context, polynomial definition, theorem type and complete
proof were read directly from the retained source.

The registered source is `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No project errata file was found for either registration.

Only this exact proof is extracted. The published statement and definition,
their Markdown, and all their imports are reused unchanged. This module
does not prove the sibling monicity target or any iterate result.

## Attribution and modifications

The Lean file retains the original 2026 copyright, Apache-2.0 release line
and author header verbatim. It reuses the existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), whose SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. The published source audit records no source-specific NOTICE
entry or third-party source-table entry for DivisionPolynomial.lean.

Worker 572 made these modifications on 16 November 2026:

- extracted only M339.006 into this focused proof module;
- changed namespace `LubinTate` to `Langlands.NYLL.LubinTate`;
- expressed the conclusion as the fully applied published `Statement` and
  added its unfolding before the unchanged original proof body;
- replaced the upstream imports by the published `DegreeStatements` and
  `Mathlib.Algebra.Polynomial.Degree.Operations`, and omitted unused
  polynomial and power-series scoped notation;
- prefixed the theorem docstring with its unit number, replaced the module
  documentation, added the modification notice, and wrote this Markdown.
