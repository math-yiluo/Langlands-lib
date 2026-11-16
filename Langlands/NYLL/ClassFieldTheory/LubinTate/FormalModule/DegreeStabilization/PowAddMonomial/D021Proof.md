# A nonconstant monomial has zero constant coefficient (NYLL M351.021)

This module proves the published proposition
`Langlands.NYLL.PortInternal.M351.d021Statement` by the theorem
`Langlands.NYLL.PortInternal.M351.d021`. Its sole import is the published
statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.Statements`,
which is not changed.

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.PortInternal.M351` and has the
target's exact binders: implicit `R : Type*` with `[CommRing R]`, implicit
`τ : Type*` (independent universes `u_1` and `u_2`), implicit `d : τ →₀ ℕ`,
the explicit hypothesis `hd : d ≠ 0` and the explicit coefficient `c : R`.
Its type is `d021Statement hd c`, which unfolds to

```
MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0
```

Mathematically: the monomial `c X^d` with a nonzero exponent `d` has zero
constant coefficient. No finiteness, decidability or local-field hypothesis is
used.

## Implemented proof

One `rw` with three rewrites:

1. `d021Statement` unfolds the target.
2. `← MvPowerSeries.coeff_zero_eq_constantCoeff_apply` rewrites the constant
   coefficient as the coefficient at the exponent `0`.
3. `MvPowerSeries.coeff_monomial_ne (Ne.symm hd)` rewrites
   `coeff 0 (monomial d c)` to `0`, using `0 ≠ d`; the goal `0 = 0` is then
   closed by `rfl`, which `rw` tries automatically.

## Source correspondence

| Original (namespace `LubinTate.SameUniformizer`) | Adapted |
| --- | --- |
| Private theorem `constantCoeff_monomial_eq_zero_stabilization`, lines 604–607 | Theorem `Langlands.NYLL.PortInternal.M351.d021`, same binders, conclusion `d021Statement hd c` |
| Line 608: `rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,` | Step 2, preceded by step 1 |
| Line 609: `MvPowerSeries.coeff_monomial_ne]` | Step 3, with the side condition supplied as an argument |
| Line 610: `exact Ne.symm hd` | The argument `Ne.symm hd` of step 3 |

## Adaptations

All modifications to the selected source declaration are:

- Make the private theorem public under the stable internal name
  `Langlands.NYLL.PortInternal.M351.d021` instead of
  `LubinTate.SameUniformizer.constantCoeff_monomial_eq_zero_stabilization`.
- State the conclusion as the published `d021Statement hd c`, unfolded by the
  first rewrite.
- Supply the side condition `0 ≠ d` of `MvPowerSeries.coeff_monomial_ne`
  directly as `Ne.symm hd` instead of closing the generated goal with
  `exact Ne.symm hd`.
- Import only the published statement module instead of the source imports
  (`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
  `Mathlib.RingTheory.MvPowerSeries.Trunc`); it supplies
  `Mathlib.RingTheory.MvPowerSeries.Basic`, which contains both rewrite
  lemmas.
- Omit the source module's other declarations, its section variables (unused
  here), `noncomputable section` and local `Classical.propDecidable` instance,
  which this proof does not need.
- Add a module title, a docstring and dated modification records.
- Worker 287 retains Worker 492's shared-draft proof unchanged and adds a
  submission provenance record dated 2026-11-16.

## Attribution, licence and environment

Worker 492 supplied the proof and paired documentation as this task's
shared draft. Worker 287 checked them against the published target and
pinned source and prepared this focused submission, retaining Worker 492
as a coauthor. The proof term is unchanged from that draft.

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by a dated modification record. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`
(SHA-256 `2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`),
readable under `n-yamaguchi-0729--ClassFieldTheory/source/` in registered
source `external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The [port partition](../../../../../../../notes/reuse/nyll-public-port/m337-m360.md#m351)
lists this unit in module M351. No patch10 edit applies.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). There the module
compiles with no errors or warnings, and the theorem has universe parameters
`u_1` and `u_2` and depends only on `propext`, `Classical.choice` and
`Quot.sound`. Compilation is not acceptance: publication under
`lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
