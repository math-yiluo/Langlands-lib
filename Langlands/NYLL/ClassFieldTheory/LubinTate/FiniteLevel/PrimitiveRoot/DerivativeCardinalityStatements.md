# Derivative-at-zero and residue-cardinality targets (M341.001, M341.002, M341.008)

This module states three Prop-valued targets from NYLL's
`PrimitiveRoot.lean`. Later work uses them to prove that the standard
primitive division polynomials are separable. In each target,
`{K : Type u} [Field K]` is implicit and the shared local-field package
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`
is explicit. The universes `u` and `v` are independent, as in the source.
`q` denotes `Nat.card F.residueField`, the cardinality of the residue
field of the chosen valuation.

| Unit | Lean declaration | Explicit parameters | Proposition |
| --- | --- | --- | --- |
| M341.001 | `Langlands.NYLL.LubinTate.standardLubinTatePolynomial_derivative_eval_zeroStatement` | `F`, `π : F.valuationSubring` | `(standardLubinTatePolynomial F π).derivative.eval 0 = π` |
| M341.002 | `Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zeroStatement` | `F`, `π : F.valuationSubring`, `n : ℕ` | `(standardLubinTatePolynomialIterate F π n).derivative.eval 0 = π ^ n` |
| M341.008 | `Langlands.NYLL.LubinTate.residueFieldNatCard_sub_one_cast_ne_zeroStatement` | `F` | `((Nat.card F.residueField - 1 : ℕ) : K) ≠ 0` |

## Mathematical content

- **M341.001.** `standardLubinTatePolynomial F π` is the polynomial
  `X ^ q + π * X` over the valuation subring. The target says that its
  formal derivative `q * X ^ (q - 1) + π`, evaluated at `0`, equals `π`.
  The equation holds in `F.valuationSubring`.
- **M341.002.** `standardLubinTatePolynomialIterate F π n` is the `n`-fold
  compositional iterate of that polynomial, starting from `X`. The target
  says that its formal derivative at `0` is `π ^ n` in `F.valuationSubring`.
- **M341.008.** The target says that the natural number `q - 1`, cast into
  the field `K`, is nonzero. Here `-` is truncated subtraction in `ℕ`, as in
  the source.

`π` is an arbitrary element of the valuation subring. No target requires it
to be a uniformizer, and the source theorems have no such hypothesis either.
No target restricts the characteristic of `K` or fixes a particular value
of `q`. The statements therefore apply to every supplied `LocalField`
package.

This pair states the targets only and proves none of them. The source
proofs use differentiation of the polynomial and induction on `n` (M341.001
and M341.002). For M341.008 they use the vanishing of `q` in the finite
residue field and the residue map from the valuation subring. Those proofs
belong to later proof units.

## Dependencies

The module imports two published definition modules:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions`,
  which defines `Langlands.NYLL.LubinTate.standardLubinTatePolynomial`
  (M339.001);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`,
  which defines `Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate`
  (M339.008).

Both definitions take `F` and `π` explicitly. Through them it also imports the
shared package `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
which supplies `F.valuationSubring` and `F.residueField`. The polynomial
definitions are used by Lean name and are not duplicated here. Two Mathlib
imports supply further API: `Mathlib.Algebra.Polynomial.Derivative` for
`Polynomial.derivative`, and `Mathlib.SetTheory.Cardinal.Finite` for
`Nat.card`.

## Source and modifications

Original source: Naganori Yamaguchi, NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

- M341.001: theorem `standardLubinTatePolynomial_derivative_eval_zero`,
  lines 44–52. The `@[simp]` attribute is at line 46, the declaration at
  line 47, the statement at lines 47–49 and the proof at lines 50–52.
- M341.002: theorem `standardLubinTatePolynomialIterate_derivative_eval_zero`,
  lines 54–69. The `@[simp]` attribute is at line 55, the declaration at
  line 56, the statement at lines 56–59 and the proof at lines 60–69.
- M341.008: theorem `residueFieldNatCard_sub_one_cast_ne_zero`, lines
  122–145. The declaration is at line 123, the statement at lines 123–125
  and the proof at lines 126–145.
- Context: lines 32–42 contain `noncomputable section`,
  `open scoped Polynomial`, `universe u v`, `namespace LubinTate`,
  `open LocalFieldTheory.DiscreteValuationField` and
  `variable {K : Type u} [Field K]`.

Worker 422 made the following modifications:

1. Kept only the statements of the three listed theorems. Every other
   declaration in the file is excluded, including the field-valued
   primitive polynomial, irreducibility, the nonzero derivative,
   separability, the chosen root and the level field.
2. Replaced each theorem by a `def` returning `Prop`. Each definition has
   the source name with the suffix `Statement`, the same parameters with
   the same explicitness and order, and the same proposition. The proofs
   and both `@[simp]` attributes are dropped.
3. Qualified the namespace as `Langlands.NYLL.LubinTate`. The source line
   `open LocalFieldTheory.DiscreteValuationField` is kept unchanged and
   resolves to `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`
   inside that namespace.
4. Replaced the source imports with focused ones. The source imports
   `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein`,
   `Mathlib.FieldTheory.IsSepClosed`,
   `Mathlib.RingTheory.Polynomial.GaussLemma` and
   `Mathlib.SetTheory.Cardinal.Finite`. This module imports
   `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`,
   `Mathlib.Algebra.Polynomial.Derivative` and
   `Mathlib.SetTheory.Cardinal.Finite`. The Eisenstein,
   separable-closure and Gauss-lemma material is not needed to state these
   three targets. The proofs need `Mathlib.FieldTheory.Finite.Basic` for
   `Nat.cast_card_eq_zero`, and the later proof units import it.
5. Replaced the module documentation and docstrings to describe targets
   instead of theorems. A modification notice was added below the original
   header.

The 2026 copyright, Apache-2.0 release and author lines of the source are
kept verbatim. The license and notices are in `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`),
and this unit does not modify them. Upstream used Lean 4.35.0-rc2. This
unit is checked in the project environment, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. No statement changed because
of the version difference.
