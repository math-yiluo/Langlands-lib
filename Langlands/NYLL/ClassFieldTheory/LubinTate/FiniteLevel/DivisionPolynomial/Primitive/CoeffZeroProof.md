# Constant coefficient of the primitive Lubin–Tate polynomial

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zeroStatement`
by the theorem
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero`.
The theorem's declared type is the fully applied imported target
`standardLubinTatePrimitivePolynomial_coeff_zeroStatement F π n`.

The telescope retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`,
`(π : F.valuationSubring)` and `(n : ℕ)`. It adds no hypothesis on `π` and
no finiteness assumption beyond the one already supplied by `F`.
The original `@[simp]` attribute is retained.

## Implemented proof

Let `q = Nat.card F.residueField` and let `fₙ` be
`standardLubinTatePolynomialIterate F π n`. The published primitive
definition is `Qₙ = fₙ ^ (q - 1) + Polynomial.C π`, with coefficients
in `F.valuationSubring`. After exposing the target equality, the proof
rewrites its constant coefficient as evaluation at zero using
`Polynomial.coeff_zero_eq_eval_zero`.

The imported theorem `standardLubinTatePolynomialIterate_eval_zero`
has its published proposition as its type. The local fact `hzero`
exposes that proposition's definition as `fₙ.eval 0 = 0`, so it can
be used as a simplification rule.
Since the residue field is a finite, nontrivial
field, `Finite.one_lt_card` gives `1 < q`; `Nat.sub_pos_of_lt` then gives
`0 < q - 1`. Simplification of polynomial evaluation and the positive
power of zero reduces `Qₙ.eval 0` to `0 + π = π`. This works also for
`n = 0` and arbitrary `π`. No additional public declarations are introduced.

The imports are the unchanged primitive target module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements`
and the published evaluation-at-zero proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.EvalZeroProof`.
The target pair and its dependencies are preserved.

## Source and attribution

The proof is adapted from Naganori Yamaguchi's M339.018 in
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`,
lines 261–271](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L261-L271),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file has SHA-256
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The complete source file, lines 1–294, was read directly.
Its supporting iterate theorem is M339.013, lines 182–196, and the
primitive definition is M339.014, lines 198–204.

The readable original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. No matching project errata
entry was found for either registration.

Worker 661 made these modifications on 16 November 2026:

- extracted only the M339.018 proof and its docstring, retaining the
  original `@[simp]` attribute;
- qualified the namespace as `Langlands.NYLL.LubinTate`;
- used the fully applied published proposition as the theorem's type,
  with a `change` step exposing its unchanged equality;
- replaced the upstream imports by the two focused published modules
  above and reused the published iterate evaluation theorem;
- exposed the imported iterate target as its evaluation equality in the
  local fact `hzero` for simplification;
- omitted the unused scoped opens, replaced the module documentation,
  and added the modification notice and this paired Markdown.

The original 2026 copyright, Apache-2.0 release line and author header
are retained verbatim. The existing [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The attribution supplement does not list this source among the
Anthropic-derived files.
