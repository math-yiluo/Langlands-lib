# The standard Lubin–Tate series

This module adapts exactly source unit M338.002, the definition
`Langlands.NYLL.LubinTate.standardLubinTateSeries`. For a uniformizer `π`
of a local field package `F`, it packages the polynomial series
`π X + X ^ q` of M338.001 (`q = Nat.card F.residueField`) as a term of
the shared structure `Langlands.NYLL.LubinTate.LubinTateSeries F π`. It is
a Type-valued construction, not an existence statement. The projection law
for its underlying series (M338.003) is a separate statement unit.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean`,
lines 42–58 (docstring and definition), with context at lines 23–32
(noncomputable section, universes, namespace, opened namespace and the
section variables `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K} {π : F.valuationSubring}`). The source-file
SHA-256 is
`2184cfbc0ef0b53881fd61f4b227147a9fe77949670c99232d4d2c3c9e9dc5df`.
The readable original is beneath
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Parameters and meaning

The declaration retains independent universes `u v`, the implicit
`K : Type u`, the instance `[Field K]`, the implicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
the implicit `π : F.valuationSubring`, and the explicit hypothesis

  `hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`,

that is, the image of `π` in `K` is a uniformizer of the chosen discrete
valuation (Mathlib's `Valuation.IsUniformizer`: its valuation is the
generator of the rank-one discrete value group). The result type is
`Langlands.NYLL.LubinTate.LubinTateSeries F π`, the shared M336.001
package. Its four fields are given exactly as in the source:

| Field | Value or proved law |
| --- | --- |
| `toPowerSeries` | `standardLubinTatePowerSeries F π`, i.e. `PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card F.residueField`. |
| `constantCoeff_eq_zero` | The constant coefficient of this series is `0`. |
| `coeff_one_eq_uniformizer` | Its coefficient of degree one is `π`. |
| `map_residue_eq_frobenius` | `PowerSeries.map F.residueMap` sends it to `PowerSeries.X ^ Nat.card F.residueField`. |

The only data field is the underlying series; the other three are proofs,
so the definition is determined by `standardLubinTatePowerSeries F π`. No
actual-characteristic or equal-characteristic assumption is made.

## The three proof fields

- `constantCoeff_eq_zero` (source lines 47–51, unchanged): the residue
  field is finite (the `LocalField` instance `residueFinite`) and nontrivial
  (it is a field), so `Finite.one_lt_card` gives `1 < q` and hence `q ≠ 0`;
  `simp` then evaluates the constant coefficient of `C π * X + X ^ q`.
- `coeff_one_eq_uniformizer` (source lines 52–55, unchanged): from
  `1 < q` it gets `1 ≠ q`, and `simp` with `PowerSeries.coeff_X_pow`
  evaluates the coefficient of degree one to `π`.
- `map_residue_eq_frobenius` (source lines 56–58, adapted): the reduction
  of `C π * X + X ^ q` is `C (residue π) * X + X ^ q`, so it suffices that
  `F.residueMap π = 0`. The source obtains this from M337.001
  `LubinTate.SameUniformizer.residueMap_uniformizer_eq_zero hπ`. Its
  proof is not yet in the Library; only its statement target
  `Langlands.NYLL.LubinTate.SameUniformizer.residueMap_uniformizer_eq_zeroStatement`
  is published. The adapted proof establishes the same fact locally:

  ```lean
  have hres : F.residueMap π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).2
      ((Valuation.mem_maximalIdeal_iff (v := F.toCompleteDVF.valuation)).2
        hπ.val_lt_one)
  simp [standardLubinTatePowerSeries, hres]
  ```

  A uniformizer has valuation `< 1` (`Valuation.IsUniformizer.val_lt_one`),
  so it lies in the maximal ideal of the valuation subring
  (`Valuation.mem_maximalIdeal_iff`), so its residue vanishes
  (`IsLocalRing.residue_eq_zero_iff`). This follows the source proof of
  M337.001 (source `CoefficientEquation.lean`, lines 33–38), which combines
  the CompleteDVF wrappers `residue_eq_zero_iff` and
  `uniformizer_mem_maximalIdeal`; those two wrappers are replaced by the
  Mathlib lemmas recorded for them in Task 6067's contract.

Because these fields are propositions, changing the third proof does not
change the defined term's data or type.

## Dependencies and modification record

The direct imports are
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.PolynomialSeries`
(M338.001, `standardLubinTatePowerSeries`),
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions`
(M336.001, `LubinTateSeries`),
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
(the shared `LocalField` and its accessors), and
`Mathlib.SetTheory.Cardinal.NatCard` (`Finite.one_lt_card`). They replace
the source import
`Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`.

The complete adaptations are:

- extraction of M338.002 alone into this definition-only module;
  M338.001 and the M338.003 projection law are separate units;
- the `Langlands.NYLL` prefix on the namespace `LubinTate`, so the source
  name `LubinTate.standardLubinTateSeries` becomes
  `Langlands.NYLL.LubinTate.standardLubinTateSeries`; the opened
  namespace `LocalFieldTheory.DiscreteValuationField` is unchanged and
  resolves to the shared `Langlands.NYLL` package;
- the focused imports described above;
- the local proof of `F.residueMap π = 0` in the field
  `map_residue_eq_frobenius`, described above, in place of the call to
  M337.001;
- a modified-file notice and replacement module documentation.

The noncomputable section, universes `u v`, the section variables of
lines 31–32, the definition's docstring, name, parameters, result type, the
underlying series and the proofs of the first two laws are retained. This
source file has no patch10 edits. The original 2026 copyright,
Apache-2.0 release line and author header are preserved. Existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No project erratum for this source was found in the current errata notes.
