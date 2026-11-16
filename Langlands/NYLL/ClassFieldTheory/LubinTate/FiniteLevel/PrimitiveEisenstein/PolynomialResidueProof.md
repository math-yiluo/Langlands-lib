# M340.001: residue reduction of the standard Lubin–Tate polynomial

This module proves the published proposition
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_map_residueStatement`
as the theorem
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_map_residue`.
Its declared type is the imported target applied to `hπ`.

The complete parameter list, in source order, is independent universes `u v`,
implicit `{K : Type u} [Field K]`, implicit
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`,
implicit `{π : F.valuationSubring}`, and explicit
`(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))`.
There is no level parameter or additional hypothesis.

Writing `q = Nat.card F.residueField`, the conclusion is
`(standardLubinTatePolynomial F π).map F.residueMap = Polynomial.X ^ q`.
Here the standard polynomial is `X ^ q + C π * X` over the valuation
subring, and `F.residueMap` reduces its coefficients to the residue field.

## Implemented proof

The proof unfolds the target and `standardLubinTatePolynomial`. The published
theorem
`Langlands.NYLL.LubinTate.SameUniformizer.residueMap_uniformizer_eq_zero hπ`
is assigned to `hzero : F.residueMap π = 0`, exposing the equality behind
its own published target definition. Polynomial mapping preserves addition,
multiplication, powers, constants and `X`, so simplification sends
`X ^ q + C π * X` to `X ^ q + C 0 * X = X ^ q`.
The simplification uses an explicit `simp only` list of these mapping and
zero identities. This is the original source argument with the target
definition additionally unfolded. The imported statement, polynomial definitions and uniformizer
theorem are used unchanged.

## Original source and adaptations

Naganori Yamaguchi, NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`,
SHA-256 `50d30d87957974e1bf1b9c297ea2b4430cd4a37ac78ab26b38c8e1895414e815`,
M340.001, lines 44–52 (the declaration begins at line 46 and its proof is
at lines 50–52). The section and namespace context is at lines 33–42.
The source is registered as
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata lookup has no
entry for this source.

Worker 194 made these adaptations:

- Extract only M340.001 into the requested proof module.
- Prefix the source namespace `LubinTate` with `Langlands.NYLL`; the opened
  `LocalFieldTheory.DiscreteValuationField` resolves under that prefix.
- Replace the source imports with the published residue-statement module and
  the published uniformizer-residue proof module.
- Preserve the full source telescope and express the conclusion as the fully
  applied imported target. Expose the prerequisite's equality as `hzero`,
  unfold the target and make the source simplification rules explicit.
- Replace the module documentation and omit the unused `noncomputable section`
  and `open scoped Polynomial`.

The original copyright, Apache-2.0 notice and author line are retained in
the Lean header. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` apply.
