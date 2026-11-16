# Residue reduction of the standard Lubin–Tate polynomial iterates (M340.002)

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_map_residue`
with the fully applied published target
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_map_residueStatement hπ n`
as its type.

The telescope retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, implicit
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`,
implicit `{π : F.valuationSubring}`, explicit
`(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))`, then explicit
`(n : ℕ)`. There are no additional hypotheses.

Put `q = Nat.card F.residueField` and
`f = standardLubinTatePolynomial F π = X ^ q + C π * X`.
The iterate is repeated polynomial composition, starting at `X`. The
theorem asserts
`(standardLubinTatePolynomialIterate F π n).map F.residueMap =
  Polynomial.X ^ (q ^ n)`.
Thus coefficient reduction of the `n`-fold iterate is precisely the stated
monomial.

## Implemented proof

After unfolding the imported target wrapper, the proof inducts on `n`.
For `n = 0`, unfolding the iterate gives `X`, and simplification reduces both
sides to `X`.

In the successor case, the imported exact theorem
`standardLubinTatePolynomialIterate_succ F π n` rewrites the successor
as `f.comp (standardLubinTatePolynomialIterate F π n)`. Mathlib's
`Polynomial.map_comp` commutes coefficient reduction with composition.
The imported exact theorem `standardLubinTatePolynomial_map_residue hπ`
reduces `f` to `X ^ q`, and the induction hypothesis reduces its inner
iterate to `X ^ (q ^ n)`. Composition of these monomials gives
`(X ^ (q ^ n)) ^ q`; `pow_mul` and `pow_succ` identify this with
`X ^ (q ^ (n + 1))`.

The two prerequisite theorems are exposed as typed local equalities so that
rewriting uses their conclusions through the imported Prop wrappers.
The proof uses their published results; it supplies no separate proof of
either prerequisite.

## Source and adaptations

The original is Naganori Yamaguchi, NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`,
SHA-256 `50d30d87957974e1bf1b9c297ea2b4430cd4a37ac78ab26b38c8e1895414e815`.
M340.002 occupies lines 54–69: the declaration begins at line 56,
the type ends at line 60, and the proof is at lines 60–69.
The header and universe/namespace context are at lines 1–42.

The source is registered as
`external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original was read from the registered snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The project errata search found no entry for this source.

Worker 784 adapted this proof on 16 November 2026:

- Prefix the namespace with `Langlands.NYLL` and retain the complete
  source parameter order and independent universes.
- State the theorem with the exact, fully applied imported `Statement`
  target, then unfold that wrapper before induction.
- Replace the original whole division-polynomial and Eisenstein imports
  with the published residue-statement module and the focused
  `DivisionPolynomial.Iterate.SuccProof` and
  `PrimitiveEisenstein.PolynomialResidueProof` modules.
- Expose the two prerequisite conclusions as typed local equalities;
  retain the source induction, `Polynomial.map_comp` and power simplification.
- Omit all other source declarations and replace the module documentation.
  Drop `open scoped Polynomial`, since this module uses no `R[X]` notation.

The original copyright, Apache-2.0 notice and author line remain in the Lean
header. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are retained unchanged.
