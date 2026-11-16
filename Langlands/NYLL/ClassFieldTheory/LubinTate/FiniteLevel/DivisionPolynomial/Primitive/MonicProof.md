# Monicity of the primitive Lubin–Tate quotient polynomial

This module proves the published target
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_monicStatement`.
Its theorem is
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_monic`,
with independent universes `u v`, implicit `{K : Type u} [Field K]`, and
explicit arguments
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`,
`(π : F.valuationSubring)` and `(n : ℕ)`. The theorem's type is the fully
applied imported target `standardLubinTatePrimitivePolynomial_monicStatement F π n`.
No uniformizer hypothesis or extra finiteness hypothesis is assumed.

Put `q = Nat.card F.residueField`, and let
`f(X) = X ^ q + π X`. The published iterate is `f^[n](X)`, starting at `X`,
and the published primitive quotient is
`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π`. The conclusion says that the leading
coefficient of `Qₙ` is `1`.

## Implemented proof

The finite nontrivial residue field supplied by `F` gives `1 < q`.
All auxiliary facts are local facts inside the theorem.

First, `f` has natural degree `q`: the term `π X` has natural degree at
most `1`, strictly less than that of `X ^ q`, so
`Polynomial.natDegree_add_eq_left_of_natDegree_lt` applies. The same
comparison of polynomial degrees and `Polynomial.Monic.add_of_left` show
that `f` is monic. These arguments work also when `π = 0`.

Next, `Polynomial.natDegree_iterate_comp` gives natural degree `q ^ m`
for each iterate. Induction on `m` proves monicity of every iterate:
the zeroth iterate is `X`, and `Function.iterate_succ_apply'` expresses
the successor as composition by `f`. `Polynomial.Monic.comp` applies
because the inner iterate has nonzero natural degree `q ^ m`.

After unfolding the target and the primitive polynomial, the power
`(f^[n]) ^ (q - 1)` is monic by `Polynomial.Monic.pow`. Its natural degree
is `(q - 1) * q ^ n`, which is positive since `1 < q`. Its polynomial
degree is therefore strictly greater than `0`, whereas the degree of
the constant polynomial `Polynomial.C π` is at most `0`.
`Polynomial.Monic.add_of_left` proves the desired monicity.

The entry module imports the published primitive `Statements` module and
`Mathlib.Algebra.Polynomial.Monic`. No imported Lean/Markdown pair is edited.
The local auxiliary calculations introduce no additional published
declarations.

## Source and attribution

The proof adapts M339.017 (docstring line 237, theorem lines 238–259) of
Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L237-L259)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The whole source file, lines 1–294, including its header, was read.
Its SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The source registrations are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No matching project errata entry was found.

The local degree and monicity arguments adapt source M339.006
(lines 100–114), M339.007 (lines 116–128), M339.011 (lines 155–163)
and M339.012 (lines 165–180). Successor recursion is performed directly
from the published iterate definition, as in M339.010 (lines 144–153).
These calculations supply the main proof's prerequisites without
importing unpublished proofs.

Worker 669 made these modifications on 16 November 2026:

- Extracted only the M339.017 theorem and its necessary local calculations.
- Prefixed the namespace with `Langlands.NYLL` and retained the complete
  source telescope, including independent universes.
- Replaced the source imports with the published primitive target module
  and the Mathlib monicity module.
- Used the fully applied imported target as the theorem's declared type.
- Replaced references to source prerequisite theorems by local facts
  derived from the published definitions; used direct iterate recursion
  instead of naming a separate successor theorem, and folded the inner
  iterate with `change` before rewriting its degree.
- Omitted the temporary abbreviation `A` in the source main proof and
  used the full iterate expression; shared `1 < q` as the local fact `hq`.
- Replaced the module documentation, added the modification notice, and
  wrote this paired Markdown.

The original 2026 copyright, Apache-2.0 release line and author header
are retained verbatim. The existing unmodified
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The attribution supplement does not list this file among the
Anthropic-derived files.
