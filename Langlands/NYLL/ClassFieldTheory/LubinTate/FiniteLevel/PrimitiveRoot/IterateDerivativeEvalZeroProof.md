# Derivative at zero of the standard iterate (M341.002)

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero`
with the exact imported target
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zeroStatement F π n`
as its declared type. The telescope retains independent universes `u v`,
implicit `{K : Type u} [Field K]`, and explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`, in that order.

Writing `q = Nat.card F.residueField`, the published standard polynomial is
`f = X ^ q + C π * X`, and its published iterate is
`f.comp^[n] Polynomial.X`. The conclusion is
`(standardLubinTatePolynomialIterate F π n).derivative.eval 0 = π ^ n`
in `F.valuationSubring`. No uniformizer, characteristic or extra finiteness
hypothesis is imposed. Finiteness of the residue field is already part of
the supplied `LocalField` package.

## Implemented proof

The proof imports only the published `DerivativeCardinalityStatements`
module. Its transitive imports provide the standard polynomial and iterate
definitions, the shared local-field package, and Mathlib's polynomial
derivative and finite-cardinality API. Their Lean/Markdown pairs are
unchanged.

All auxiliary facts are local to the theorem:

1. `Finite.one_lt_card` gives `1 < q` because the residue field is a finite
   nontrivial field. Hence `q` and `q - 1` are nonzero natural numbers.
2. Simplification of the standard polynomial gives `f.eval 0 = 0`.
   Simplification of its formal derivative, using
   `Polynomial.derivative_pow`, gives `f.derivative.eval 0 = π`; the
   derivative contribution from `X ^ q` vanishes because `q - 1 ≠ 0`.
3. Unfolding the iterate and applying `Function.iterate_succ_apply'`
   gives `f^[m+1] = f.comp (f^[m])`, where the notation here denotes
   polynomial composition starting from `X`.
4. Joint induction proves both `(f^[m]).eval 0 = 0` and
   `(f^[m]).derivative.eval 0 = π ^ m`. The zero iterate is `X`.
   For the successor, `Polynomial.eval_comp` proves zero evaluation.
   `Polynomial.derivative_comp`, `Polynomial.eval_mul` and
   `Polynomial.eval_comp` express the derivative at zero as the product
   of the previous iterate's derivative at zero and `f.derivative.eval 0`.
   The induction hypotheses and the scalar computation reduce this to
   `π ^ m * π = π ^ (m + 1)`, which is `pow_succ`.

The theorem extracts the second component of this induction. These local
computations replace the upstream proof's appeals to separate recursion,
zero-evaluation and standard-polynomial derivative theorems. They introduce
no additional public declaration or hypothesis. The upstream `@[simp]`
attribute is retained on the exact-target theorem.

## Source and modifications

Adapted from Naganori Yamaguchi, NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
M341.002 occupies lines 54–69: its simp attribute is at line 55,
declaration at lines 56–59 and proof at lines 60–69. The local derivative
computation follows M341.001, lines 44–52. The local recursion and
zero-evaluation computations follow directly from the published definitions
and Mathlib and serve only as internal steps of this proof.

Registered sources:
`external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 334 made the following modifications:

- Extracted only M341.002 into this focused proof module and qualified its
  namespace as `Langlands.NYLL.LubinTate`.
- Declared the theorem using the fully applied published Prop-valued target,
  preserving its entire telescope and conclusion.
- Replaced the source imports by the published statement module, without
  importing unpublished prerequisite proofs.
- Used local scalar computations and joint induction as described above,
  retaining the source chain-rule and `pow_succ` argument.
- Added module documentation and this explanation of the implemented proof.

The original copyright, author and Apache-2.0 header is preserved verbatim
before the modification notice. Existing `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are unchanged. Upstream used Lean 4.35.0-rc2; this proof is checked in the
project's Lean 4.34.0 environment with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
