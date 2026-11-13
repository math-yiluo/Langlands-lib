# NYLL M307.002–.006: valuation-ring independence of lower and upper ramification

This module extracts M307.002 lines 50–147; .003 lines 151–163; .004 lines 168–184; .005 lines 188–204; .006 lines 208–228; section parameters lines 23–35 from Naganori Yamaguchi's *ClassFieldTheory*,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteGaloisLevelIndependence.lean` (whole-file SHA-256 `67f3ed98315313d33a9588b38e274e5ea310886ea00cda103b51a489775393a2`).
The original copyright and author header is preserved. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its Apache-2.0 attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found in the Library errata filenames.

## Exact proposition and source correspondence

All definitions below lie in `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`. Each original theorem name is
prefixed with `Langlands.NYLL` and gains the suffix `Statement`. Their full
proposition bodies, including every source parameter and hypothesis, are:

```lean
def lowerRamificationGroup_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring) (s : ℝ),
    lowerRamificationGroup (base := base) (target := target) huniq s =
      lowerRamificationGroup (base := base) (target := target') huniq' s

def lowerRamificationFiltration_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq =
      lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target') huniq'

def herbrandFunction_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq =
      herbrandFunctionOfUniqueExtension (base := base) (target := target') huniq'

def inverseHerbrandFunction_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring),
    inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq =
      inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target') huniq'

def upperRamificationGroup_eq_of_valuationSubring_eqStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    {target' : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, y} L}
    [base.valuation.HasExtension target.valuation]
    [base.valuation.HasExtension target'.valuation]
    [FiniteDimensional K L]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring) (t : ℝ),
    upperRamificationGroupOfUniqueExtension (base := base) (target := target) huniq t =
      upperRamificationGroupOfUniqueExtension (base := base) (target := target') huniq' t
```

The five source comparisons retain all five independent universes and both supplied extension instances. Equality of the target valuation rings gives equality of the real lower groups and integral lower filtrations without a finiteness assumption. Equality of the actual Herbrand functions, inverses and upper groups additionally retains FiniteDimensional K L. Each uniqueness predicate is instantiated at its own target value-group universe, x and y respectively. These statements require only the published generic filtration and Herbrand definitions, without the chosen finite-Galois-level constructions of M306 or the later M307.007–.016.

## Modifications and dependency boundary

Worker 296 extracted the displayed source signatures into closed `def`s returning
`Prop`: section parameters and theorem binders now occur under `∀` inside the
proposition. The source binder kinds and parameter order are retained, as are all
independent universe levels and hypotheses. The proofs, theorem attributes and
unused surrounding declarations are omitted. The namespace gains the prefix
`Langlands.NYLL`. Source names for the two DVF namespaces are expanded to the
published qualified names; Mathlib constants keep their original meaning.

The source's whole-module imports are replaced by exactly these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions`.

These are proposition targets; this module supplies no proof of them. In
particular, it adds no premise assuming its conclusion and no global instance.
The targets refer directly to the published data with the corresponding Lean
names. Compilation and proposition inspection are development evidence only;
independent semantic acceptance and publication remain required.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with hashes `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No feasibility proof patch or unpublished draft is reused here. The target
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
