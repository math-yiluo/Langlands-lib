# Mapped standard Lubin–Tate polynomial iterates

This definition unit contains exactly M342.001–002 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. It extends coefficients of the
standard polynomial iterate from the chosen valuation ring to the base field
and its separable closure.

## Source and attribution

The original is
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveTorsion.lean`,
SHA-256
`b34ddd5a90a7139adf81c1076b0ddd447956828e03a9d016d2712ce0b882c95c`.
The full source is readable at
[/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveTorsion.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveTorsion.lean>).

The registered source IDs are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original 2026 copyright, Apache-2.0 release line, and authorship line remain
in the Lean header. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are preserved.

## Exact correspondence

Both definitions have implicit `{K : Type u} [Field K]` and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`,
`(π : F.valuationSubring)`, and `(n : ℕ)`. The field universe `u` and
chosen value-group universe `v` remain independent. There is no uniformizer
hypothesis or choice of a different valuation.

| Source unit and line | Adapted Lean name | Result |
| --- | --- | --- |
| M342.001, line 39 | `Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterateOverField` | `Polynomial K` |
| M342.002, line 47 | `Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure` | `Polynomial (SeparableClosure K)` |

For M342.001 the body is exactly

```lean
(standardLubinTatePolynomialIterate F π n).map
  (algebraMap F.valuationSubring K)
```

For M342.002 the body is exactly

```lean
(standardLubinTatePolynomialIterate F π n).map
  ((algebraMap K (SeparableClosure K)).comp
    (algebraMap F.valuationSubring K))
```

The maps are the canonical inclusion from the chosen valuation subring into
`K` and its composite with the canonical algebra map into Mathlib's
`SeparableClosure K`. The existing polynomial iterate, LocalField package,
valuation ring, and separable closure are reused directly.

## Imports and modifications

1. Extract only the two noncomputable definitions and their documentation from
   source lines 37–53. Later source assertions are outside this unit.
2. Replace `namespace LubinTate` by `namespace Langlands.NYLL.LubinTate`, and
   qualify the opened local-field namespace with `Langlands.NYLL`.
3. Replace the original sole import
   `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot` by
   `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`
   and `Mathlib.FieldTheory.IsSepClosed`. The first supplies the polynomial
   iterate and its existing LocalField dependency; the second supplies the
   canonical separable closure. Chosen roots and primitive-root existence
   assertions are not dependencies of these two definitions.
4. Replace the original module documentation by a description of the extracted
   definitions, normalize blank lines, and add the modification notice. Retain
   the original `noncomputable section`, `open scoped Polynomial`, independent
   universes, parameter implicitness, docstrings, and definition bodies.

No theorem or Prop target is introduced, and no evaluation, torsion, primitive
root, or extension-field assertion is claimed.
