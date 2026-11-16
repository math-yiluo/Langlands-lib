# Low-degree coefficients of `(H + c X^d) ^ n` (NYLL M351.023)

This module proves the published proposition
`Langlands.NYLL.PortInternal.M351.d023Statement` by the theorem
`Langlands.NYLL.PortInternal.M351.d023`. Its sole import is the published
proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.D022Proof`
of M351.022, which imports the unchanged statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.Statements`.

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.PortInternal.M351` and has the
target's exact binders, the same as those of M351.022: implicit `R : Type*`
with `[CommRing R]`, implicit `τ : Type*` (independent universes `u_1` and
`u_2`), implicit `H : MvPowerSeries τ R`, then
`hH : MvPowerSeries.constantCoeff H = 0`, `q d : τ →₀ ℕ`,
`hq : q.degree ≤ d.degree`, `hd : 1 ≤ d.degree`, `c : R` and `n : ℕ`, all
explicit. Its type is `d023Statement hH q d hq hd c n`, which unfolds to

```
MvPowerSeries.coeff q ((H + MvPowerSeries.monomial d c) ^ n) =
  MvPowerSeries.coeff q (H ^ n) +
    if n = 1 then (if q = d then c else 0) else 0
```

Mathematically: under the hypotheses of M351.022, in every exponent `q` of
total degree at most `d.degree` the coefficient of `(H + c X^d) ^ n` is that
of `H ^ n`, plus `c` when `n = 1` and `q = d`.

## Implemented proof

1. `h := d022 hH q d hq hd c n` is M351.022 for the same arguments;
   `unfold d022Statement at h` exposes it as
   `coeff q (A ^ n - H ^ n) = E`, where `A = H + monomial d c` and `E` is the
   conditional term.
2. `unfold d023Statement` exposes the goal `coeff q (A ^ n) = coeff q (H ^ n) + E`.
3. `rw [map_sub, sub_eq_iff_eq_add] at h` turns `h` into
   `coeff q (A ^ n) = E + coeff q (H ^ n)`.
4. `rw [h, add_comm]` rewrites the goal to `coeff q (H ^ n) + E = coeff q (H ^ n) + E`,
   closed by `rfl`.

## Source correspondence

The original is the private theorem
`LubinTate.SameUniformizer.coeff_pow_add_monomial_of_degree_le`, type at
lines 682–691 and proof at lines 692–696.

| Original | Adapted |
| --- | --- |
| Lines 682–691: binders and conclusion | Same binders; conclusion `d023Statement hH q d hq hd c n` |
| Lines 692–694: `have h := coeff_pow_add_monomial_sub_pow_of_degree_le hH q d hq hd c n` | Step 1, citing `Langlands.NYLL.PortInternal.M351.d022` and unfolding its statement |
| Line 695: `rw [map_sub, sub_eq_iff_eq_add] at h` | Step 3, unchanged |
| Line 696: `simpa [add_comm] using h` | Steps 2 and 4: `rw [h, add_comm]` |

## Adaptations

All modifications to the selected source declaration are:

- Make the private theorem public under the stable internal name
  `Langlands.NYLL.PortInternal.M351.d023` instead of
  `LubinTate.SameUniformizer.coeff_pow_add_monomial_of_degree_le`.
- State the conclusion as the published `d023Statement hH q d hq hd c n`,
  opened by `unfold`.
- Cite M351.022 by its published name `Langlands.NYLL.PortInternal.M351.d022`
  and unfold its statement at the hypothesis.
- Close the goal by `rw [h, add_comm]` instead of `simpa [add_comm] using h`.
- Import only the published M351.022 proof module instead of the source
  imports (`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
  and `Mathlib.RingTheory.MvPowerSeries.Trunc`).
- Omit the source module's other declarations, its unused section variables
  `K`, `F`, `π`, `σ` and `[Fintype σ]`, `noncomputable section`,
  `open scoped BigOperators`, `universe u v w`,
  `open LocalFieldTheory.DiscreteValuationField` and local
  `Classical.propDecidable` instance; the statement module fixes the
  decidability of `q = d`.
- Add a module title, a docstring and a dated modification record.

## Attribution, licence and environment

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

Worker 492 supplied the proof draft; Worker 573 prepared this focused
contribution, checked the source and inherited licence hashes, and retained
the implemented proof.

The approved development environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). After M351.022 was published, the
module compiled there with no errors or warnings. Declaration inspection
reports independent universe parameters `u_1` and `u_2` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. A separate private module also
compiled a direct assignment of the unapplied constant `@d023` to the complete
target telescope, with independent universes and no supplied arguments. The
published statement's Lean and Markdown files are unchanged.

These are development checks. Publication under `lean.proof@1` also requires
the Lake build, exact-target and unchanged-statement checks, independent
semantic review and integration.
