# The abstract norm of a finite fixed field: targets (M166.002–M166.004)

This module states three NYLL source theorems without proof. It exports three
Prop-valued `def`s in the namespace `Langlands.NYLL.LocalClassFieldTheory`:

- `normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement` (M166.002);
- `localBaseValuation_normToBase_abstractFixedFieldUnitStatement` (M166.003);
- `localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement`
  (M166.004).

Each is a binder-style definition: its binders are the binders of the source
theorem, and its body is the theorem's type. A proof of a target for given
arguments is a proof of the source theorem for those arguments. The proofs
are later units under the source theorem names in the same namespace, without
the suffix `Statement`.

## Setting

Let `Ω` be a separably closed field that is Galois over a field `K`, let
`G = Gal(Ω/K)`, and let `H` be a closed subgroup of `G`. The abstract
class-formation framework represents a field by a closed subgroup. The
concrete field represented by `H` is its fixed field
`E = abstractFixedField K Ω H = Ω^H`, an intermediate field of `Ω/K`.

The units `Ωˣ`, written additively, form the integral `G`-representation
`galoisAmbientUnitsRep K Ω`. For a closed subgroup `C`, the elements fixed by
`C` form `ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) C`. The base
field is represented by the whole group `baseField G`, so its fixed elements
are the units of `Ω` fixed by all of `G`.

- `abstractFixedFieldUnitsEquivGaloisFixed K Ω H` is the additive
  isomorphism from `Additive Eˣ` to the `H`-fixed elements. It sends a unit
  of `E` to the same element of `Ω`.
- If `H` has finite index in `G`, `normToBase (galoisAmbientUnitsRep K Ω) H`
  is the class-formation norm from the `H`-fixed elements to the `G`-fixed
  elements. In additive notation it sums the translates `σ · y` over left
  coset representatives `σ` of `H` in `G`. Multiplicatively, it takes the
  product of the conjugates `σ(y)`.

So M166.002 compares this abstract norm with the field norm
`Algebra.norm K : E → K`. M166.003 and M166.004 specialize to a
nonarchimedean local field `K` with `Ω = SeparableClosure K`. There the
published `localBaseValuation K` is NYLL's valuation of `K` on the `G`-fixed
units, cast into the profinite integers `ℤ̂ = ZHat`.

**Sign convention.** NYLL's `valuationMap` is the *negative* of the usual
normalized discrete order `ord`, for which a prime element `π` of the
valuation ring `𝒪[K]` has `ord(π) = 1`; so `valuationMap K x = -ord(x)`. It
is built from Mathlib's order-preserving isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` onto
`WithZero (Multiplicative ℤ)`, so elements of valuation less than one get
negative integers. In particular a prime element of `𝒪[K]` has value `-1`.
The published Markdown of
[`localBaseValuation`](../../HenselianValuationBase/U001/Definitions.md)
and the published audit
[`notes/reuse/nyll-finite-local-reciprocity-audit.md`](../../../../../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md)
(section 2.3) record the same convention. The word "normalized" in the
docstrings below refers to this map. M166.003 compares two values of the same
map, so it holds or fails for either sign. M166.004 is an equality of value
sets, which negation maps onto themselves, so the sign does not affect it.

## The propositions

### `normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement` (M166.002)

```lean
def normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (H : ClosedSubgroup (Gal(Ω/K)))
    [Finite ((baseField (Gal(Ω/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) : Prop :=
  ((Additive.toMul
    ((normToBase (galoisAmbientUnitsRep K Ω) H
      (abstractFixedFieldUnitsEquivGaloisFixed K Ω H
        (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
    algebraMap K Ω (Algebra.norm K
      (x : abstractFixedField K Ω H))
```

Assume `H` has finite index in `G`, and `E = Ω^H` is finite-dimensional and
separable over `K`. Let `x` be a unit of `E`. Then the abstract norm of `x`,
viewed as an element of `Ω`, is the image in `Ω` of the field norm
`N_{E/K}(x) ∈ K`. In other words, the product of the conjugates of `x` over
the cosets of `H` is the field norm.

The finite-index instance is the source's
`Finite (G ⧸ extensionSubgroup (baseField G) H (le_baseField H))`. Here
`baseField G` is `G` as a closed subgroup, `le_baseField H` is the proof that
`H ≤ G`, and `extensionSubgroup` views `H` as a subgroup of `baseField G`.
It is the instance `normToBase` requires.

### `localBaseValuation_normToBase_abstractFixedFieldUnitStatement` (M166.003)

```lean
def localBaseValuation_normToBase_abstractFixedFieldUnitStatement
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) : Prop :=
  localBaseValuation K
      (normToBase
        (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))) =
    Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul
          (normUnits K (abstractFixedField K (SeparableClosure K) H) x)))
```

Let `K` be a nonarchimedean local field, `G = Gal(K^sep/K)` with
`K^sep = SeparableClosure K`, and `H` a closed subgroup of finite index whose
fixed field `E` is finite-dimensional over `K`. For a unit `x` of `E`, the
`localBaseValuation` of the abstract norm of `x` equals
`valuationMap K (N_{E/K}(x))` cast into `ℤ̂`. Here
`normUnits K E x = N_{E/K}(x)` is the field norm on units. The source theorem
has no separability binder; `E` lies in `K^sep`.

The published `localBaseValuation K` is defined on
`ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
(baseField (intrinsicAbsoluteGalois K))`. The published abbreviations
`intrinsicAbsoluteGalois K = Gal(SeparableClosure K / K)` and
`intrinsicAbsoluteUnits K = galoisAmbientUnitsRep K (SeparableClosure K)`
(M091.001, M091.002) make this the codomain of `normToBase` above, by
unfolding.

### `localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement` (M166.004)

```lean
set_option linter.unusedVariables false in
def localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] : Prop :=
  ((localBaseValuation K).comp
    (normToBase
      (galoisAmbientUnitsRep K (SeparableClosure K)) H)).range =
    nsmulImage (localBaseValuation K).range
      (Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (SeparableClosure K) H])
```

Take `K`, `H` and `E` as in M166.003, and give `E` its own nonarchimedean
local field structure (a `ValuativeRel`, a topology and Mathlib's
`IsNonarchimedeanLocalField`). Assume two compatibility conditions:

- Mathlib's `Valuation.HasExtension` says that the valuation of `E`,
  restricted to `K`, is equivalent to the valuation of `K`;
- `𝒪[E]` is the integral closure of `𝒪[K]` in `E`.

Let `f` be the residue degree, the dimension of the residue field `𝓀[E]`
over `𝓀[K]`. The target says that the values of `localBaseValuation K` on
the abstract norms of `H`-fixed units are exactly `f` times the values of
`localBaseValuation K`. That is, `v_K(N_{E/K}(Eˣ)) = f · v_K(Kˣ)` as subsets
of `ℤ̂`, where `nsmulImage Z f` is the image of `Z` under `z ↦ f • z`.

`𝒪[F]` and `𝓀[F]` are Mathlib's scoped `ValuativeRel` notation for the
valuation ring `(ValuativeRel.valuation F).integer` and its residue field
`IsLocalRing.ResidueField 𝒪[F]`. Lean finds the remaining structure by
instance search: the `𝒪[K]`-algebra structure on `𝒪[E]` is
`Valuation.HasExtension.instAlgebraInteger` (from the `HasExtension`
instance), and the `𝓀[K]`-algebra structure on `𝓀[E]`, which gives the
module in `Module.finrank`, is `IsLocalRing.ResidueField.instAlgebra`. A
private probe printed both names.

The instance binder `hIntegralClosure` does not occur in the proposition. It
is a binder of the definition, so the proposition is asserted only for data
satisfying it, exactly as for the source theorem. The source names it and
its proof uses it. `set_option linter.unusedVariables false in` only
silences the linter warning about the name and does not change the
definition. The published Library uses the same option for the same reason,
for example in the sibling module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U001.Statements`.

## Published declarations used

All names below are published in the Library or Mathlib.

| Name | Source unit | Module |
| --- | --- | --- |
| `Langlands.NYLL.ClassFormation.baseField` | M010.003 | [Degree/Fields](../../../../../AbstractClassFieldTheory/Degree/Fields/Definitions.md) |
| `Langlands.NYLL.ClassFormation.le_baseField` | M010.005 | [Degree/Fields/U005 proof](../../../../../AbstractClassFieldTheory/Degree/Fields/U005/Proofs.md) |
| `Langlands.NYLL.CyclicCohomology.extensionSubgroup` | M004.002 | [NormKernelVanishing/Extension](../../../../../../GaloisCohomology/Cyclic/NormKernelVanishing/Extension/Definitions.md) |
| `Langlands.NYLL.ClassFormation.normToBase` | M025.001 | [Degree/Valuation/ValuationData](../../../../../AbstractClassFieldTheory/Degree/Valuation/ValuationData/Definitions.md) |
| `Langlands.NYLL.ClassFormation.nsmulImage` | M025.004 | [Degree/Valuation](../../../../../AbstractClassFieldTheory/Degree/Valuation/Definitions.md) |
| `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` | M088.001 | [AbsoluteUnitsFixedField/Initial](../../AbsoluteUnitsFixedField/Initial/Definitions.md) |
| `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` | M099.001 | [FiniteAbstractFixedField/Initial](../../FiniteAbstractFixedField/Initial/Definitions.md) |
| `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | M101.001 | [AbstractFixedFieldUnits/Initial](../../AbstractFixedFieldUnits/Initial/Definitions.md) |
| `Langlands.NYLL.LocalClassFieldTheory.localBaseValuation` | M163.005 | [HenselianValuationBase/U001](../../HenselianValuationBase/U001/Definitions.md) |
| `Langlands.NYLL.LocalFieldTheory.normUnits` | M092.002 | [NormUnits/U002](../../../../../../ValuedFieldTheory/LocalField/NormUnits/U002/Definitions.md) |
| `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | M134.002 | [ValuationExactSequence](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence/Definitions.md) |
| `Langlands.NYLL.ClassFormation.ZHat` | M008.008 | [ProfiniteIntegerCore](../../../../../../GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Definitions.md) |

`normToBase A K` is the published relative norm
`relativeNorm A (baseField G) K (le_baseField K)`. `nsmulImage Z n` is the
image of the subgroup `Z` of `ℤ̂` under `z ↦ n • z`. `normUnits K L` is
`Units.map (Algebra.norm K)`. Mathlib supplies `ClosedSubgroup`, `Gal(Ω/K)`,
`IsGalois`, `IsSepClosed`, `SeparableClosure`, `Algebra.norm`,
`Algebra.IsSeparable`, `FiniteDimensional`, `IsNonarchimedeanLocalField`,
`ValuativeRel`, `Valuation.HasExtension`, `IsIntegralClosure`,
`Module.finrank`, `Int.castRingHom` and `AddMonoidHom.range`.

## Source and binders

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean),
SHA-256 `f4529e6c10db2c36c8c1dd88506cb999bd030618c1800f1d1ab96ab604e5f4fd`.
The relevant lines are:

- the namespace and opens, lines 21–28: `namespace LocalClassFieldTheory`,
  `open RamificationTheory CyclicCohomology KummerTheory ClassFormation`,
  `open LocalFieldTheory`, `noncomputable section`;
- `open scoped ValuativeRel` and the section variables
  `(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]`,
  lines 30–32;
- M166.002: docstring lines 65–67, theorem lines 68–80 (binders and type);
  the proof from line 81 is omitted;
- M166.003: docstring lines 108–109, theorem lines 110–128 (binders and
  type); the proof from line 129 is omitted;
- M166.004: docstring lines 172–174, theorem lines 175–199 (binders and
  type); the proof from line 200 is omitted.

M166.002 uses the section variables, so Lean includes `K`, `Ω` and their
five instance binders in the source theorem, first and in this order. The
target takes them as its leading binders, followed by the theorem's own
binders. M166.003 and M166.004 declare their own `K : Type`, which shadows
the section variable. They mention neither the section `K` nor `Ω`, so Lean
includes no section variable, and the targets take exactly the theorems'
own binders. The probe below checks both points.

In all three targets the binders, their kinds (explicit or instance), their
names (including `hIntegralClosure`) and their order are the source text, and
the bodies are the source types verbatim. `K` and `Ω` live in `Type`, as in
the source, so there are no universe parameters.

## Declaration map

The Library's `notes/errata/` has no NYLL entry. Rows M166.002–M166.004 of the
published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserve the adapted names without the `Statement` suffix for the proofs. No
declaration of the target names exists in the current Library or Mathlib.

| Original declaration | Adapted declaration |
| --- | --- |
| theorem `LocalClassFieldTheory.normToBase_abstractFixedFieldUnit_val_of_isSeparable` (M166.002), type only | `Langlands.NYLL.LocalClassFieldTheory.normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement` (this module) |
| theorem `LocalClassFieldTheory.localBaseValuation_normToBase_abstractFixedFieldUnit` (M166.003), type only | `Langlands.NYLL.LocalClassFieldTheory.localBaseValuation_normToBase_abstractFixedFieldUnitStatement` (this module) |
| theorem `LocalClassFieldTheory.localBaseValuation_comp_normToBase_range_eq_residueFinrank` (M166.004), type only | `Langlands.NYLL.LocalClassFieldTheory.localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement` (this module) |

The used declarations are mapped in the table above.

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`,
  for `normToBase`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions`,
  for `nsmulImage`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`,
  for `le_baseField` (and through it `baseField`);
- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  for `extensionSubgroup`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions`,
  for `abstractFixedFieldUnitsEquivGaloisFixed`, and through its imports
  `abstractFixedField` and `galoisAmbientUnitsRep`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U001.Definitions`,
  for `localBaseValuation`, and through its imports `ZHat`, the intrinsic
  absolute data and `SeparableClosure`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
  for `normUnits`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`,
  for `valuationMap`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension`
  and its instances.

These replace the source's three NYLL imports (`AbstractFixedFieldUnits`,
`HenselianValuationBase` and `SeparableFixedFieldNorm`). Every transitive
import lies in the approved Mathlib environment or the published Library.

Worker 85 extracted these statements on 15 November 2026. The Lean header
records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`, and the suffix `Statement` is
  added to each name;
- each theorem becomes a Prop-valued definition whose binders are the
  theorem's binders (for M166.002 preceded by the included section
  variables) and whose body is the theorem's type;
- `set_option linter.unusedVariables false in` is added before the M166.004
  definition, as explained above;
- the proofs are omitted; they belong to later proofs;
- the source opens are kept: `open RamificationTheory CyclicCohomology
  KummerTheory ClassFormation`, `open LocalFieldTheory` and `open scoped
  ValuativeRel`. Inside the new namespace they resolve to the
  `Langlands.NYLL` namespaces that supply the used names, and the scoped
  `ValuativeRel` notation supplies `𝒪[·]` and `𝓀[·]`. The
  `noncomputable section` and the section variables are not kept;
- the imports are replaced as described above.

The propositions are unchanged. Every other source declaration is omitted.
No theorem, instance, notation or alias is introduced.

## Checks

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports each target
as a definition without level parameters whose type returns `Prop`, using
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

A private probe, not part of this module, also compiled with zero errors. It
declares the source section variables of lines 31–32 and then restates the
binders of M166.002 and M166.003 inside that section. The resulting
signatures agree with those of the targets, so the targets take exactly the
binders Lean gives the source theorems. The probe also printed the two
instance names above and checked by `rfl` that
`intrinsicAbsoluteUnits K = galoisAmbientUnitsRep K (SeparableClosure K)`.
These development checks are not independent acceptance.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. Worker 85
adapted this unit directly from the pinned original; no other project
worker supplied code.
