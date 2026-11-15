# The base value group of a local field in `ℤ̂`: proofs (M163.004, M163.006–M163.008, M163.010, M163.011, M163.013)

This module proves the seven closed proposition targets of the published
[statement module](Statements.md)
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U004.Statements`,
in the namespace `Langlands.NYLL.LocalClassFieldTheory`. The targets have no
universe parameters, and neither do the theorems:

```lean
theorem baseFieldUnitsEquiv_val : baseFieldUnitsEquiv_valStatement
theorem localBaseValuation_baseFieldUnitsEquiv :
    localBaseValuation_baseFieldUnitsEquivStatement
theorem localBaseValuation_range : localBaseValuation_rangeStatement
theorem intToProCInteger_mem_localBaseValuation_range :
    intToProCInteger_mem_localBaseValuation_rangeStatement
theorem localValueGroupReduction_surjective :
    localValueGroupReduction_surjectiveStatement
theorem localValueGroupReduction_ker : localValueGroupReduction_kerStatement
theorem localCanonicalValueQuotientMap_bijective :
    localCanonicalValueQuotientMap_bijectiveStatement
```

These are the proof phases of M163.004, M163.006, M163.007, M163.008,
M163.010, M163.011 and M163.013 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m163).
Each theorem name is the source theorem name in the prefixed namespace.
After the first two theorems the module also adds two explicit-telescope
`@[simp]` wrappers, `baseFieldUnitsEquiv_val_apply` and
`localBaseValuation_baseFieldUnitsEquiv_apply`, described in
[Simp attributes](#simp-attributes). No other declaration is added.

## Setting and sign convention

`K : Type` is a field; except in M163.004 it is a nonarchimedean local field,
with `[ValuativeRel K]`, `[TopologicalSpace K]` and Mathlib's
`[IsNonarchimedeanLocalField K]` in this order. Write `K^sep` for
`SeparableClosure K`, `ℤ̂` for `ZHat`, and `A^G` for the fixed coefficient
group
`ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K))`
of `Additive (K^sep)ˣ`. The published
[definitions module](../U001/Definitions.md) (M163.003, M163.005, M163.009)
defines:

- `baseFieldUnitsEquiv K : Additive Kˣ ≃+ A^G`, the published M096.001
  equivalence `baseUnitsEquivGaloisAmbientFixed K K^sep` followed by the
  `AddEquiv.addSubgroupCongr` along the equality of the closed fixing
  subgroup of `⊥` with the base subgroup;
- `localBaseValuation K : A^G →+ ℤ̂`, the composite of
  `(baseFieldUnitsEquiv K).symm`, NYLL's `valuationMap K : Additive Kˣ →+ ℤ`
  (M134.002) and `Int.castRingHom ZHat`;
- `localValueGroupReduction K n hn : (localBaseValuation K).range →+ ZMod n`,
  the subgroup inclusion into `ℤ̂` followed by `zHatReduction n hn`.

Write `Z = (localBaseValuation K).range`, the value group.

**Sign convention.** NYLL's `valuationMap` is the **negative** of the usual
normalized order `ord`: a prime element of the valuation ring `𝒪[K]` has
value `-1`, and its inverse has value `1`. So, by M163.006 and this
convention, `localBaseValuation K` sends the element
`baseFieldUnitsEquiv K (Additive.ofMul π)` corresponding to a prime element
`π` to `-1` in `ℤ̂`, not to `1`. The paired
Markdown of the [statement module](Statements.md), section 2.3 of the
published audit
[`notes/reuse/nyll-finite-local-reciprocity-audit.md`](../../../../../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md)
and the [definitions module](../U001/Definitions.md) record the same
convention. The other six results do not depend on the sign: M163.004 does
not involve the valuation, and the rest concern only the value group `Z`,
the image of `ℤ` in `ℤ̂`, which negation maps onto itself. None of the
proofs uses the sign.

## The proofs

Every proof starts with `intro`, introducing the source section variables
`K` and its instances (only `K` and `[Field K]` for M163.004) and then the
theorem's own binders. Then it runs the source proof. Inside the proofs, the
earlier closed theorems of this module are applied to explicit arguments or
used by `rw`, as the source does.

### `baseFieldUnitsEquiv_val` (M163.004)

After `intro K _ x`, a `change` (the source's) rewrites the goal to the value
equation for `baseUnitsEquivGaloisAmbientFixed K K^sep` at
`Additive.ofMul x`. This is definitional: `addSubgroupCongr` does not change
the underlying element. The published M096.002 theorem
`baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K) x`, whose type is
that equation, closes it by `exact`. The instance `IsGalois K K^sep` that
M096.002 requires is found by instance search (Mathlib's
`IsSepClosure.isGalois`).

### `localBaseValuation_baseFieldUnitsEquiv` (M163.006)

After `intro K _ _ _ _ x`, `simp [localBaseValuation]` unfolds the composite
and cancels `(baseFieldUnitsEquiv K).symm (baseFieldUnitsEquiv K x) = x`.
This is the source proof unchanged.

### `localBaseValuation_range` (M163.007)

By `le_antisymm`, as in the source.

- `⊆`: a value `localBaseValuation K x` is, by definition, the cast of the
  integer `valuationMap K ((baseFieldUnitsEquiv K).symm x)`; the anonymous
  constructor with `rfl` gives membership in the range of the cast.
- `⊇`: for an integer `m`, the published M134.005 theorem
  `valuationMap_surjective K m` gives `x : Additive Kˣ` with
  `valuationMap K x = m`. The witness is `baseFieldUnitsEquiv K x`;
  `rw [localBaseValuation_baseFieldUnitsEquiv, hx]` (M163.006 above) and
  `rfl` finish.

### `intToProCInteger_mem_localBaseValuation_range` (M163.008)

After `intro K _ _ _ _ m`, `rw [localBaseValuation_range]` (M163.007 above)
turns the goal into membership of `Int.castRingHom ZHat m` in the range of
the cast, and `⟨m, rfl⟩` proves it.

### `localValueGroupReduction_surjective` (M163.010)

Given `a : ZMod n`, Mathlib's `ZMod.intCast_surjective` writes `a = (m : ZMod n)`
for an integer `m`. The preimage is the value
`⟨Int.castRingHom ZHat m, intToProCInteger_mem_localBaseValuation_range K m⟩`
of `Z` (M163.008 above). Its reduction is definitionally
`zHatReduction n hn (Int.castRingHom ZHat m)`, and the published M009.007
theorem `zHatReduction_int n hn m`, whose type unfolds to
`zHatReduction n hn (m : ZHat) = (m : ZMod n)`, closes the goal by `exact`.

### `localValueGroupReduction_ker` (M163.011)

By `le_antisymm`, as in the source.

- `ker ≤ nZ`: let `z ∈ Z` reduce to `0`. Rewriting with M163.007,
  `(z : ℤ̂) = Int.castRingHom ZHat m` for an integer `m` (equation `hm`). The
  reduction hypothesis is changed to `zHatReduction n hn (z : ℤ̂) = 0`,
  rewritten by `← hm`, and composed with the reversed equation
  `zHatReduction_int n hn m` to give `(m : ZMod n) = 0`. **Adaptation:** the
  source does this step by `rw [← hm, zHatReduction_int] at hz0; exact hz0`.
  The published `zHatReduction_int` proves
  `zHatReduction_intStatement n hn m`, an alias of the M008.019 equation
  `zHatReduction n hn (m : ZHat) = (m : ZMod n)` stated with the cast
  `Int.cast`, whereas `hz0` contains `Int.castRingHom ZHat m`. The two terms
  are definitionally but not syntactically equal, so that `rw` finds no
  occurrence of the left side and fails (a private probe confirmed this). The
  module therefore uses
  `rw [← hm] at hz0; exact (Eq.symm (zHatReduction_int n hn m)).trans hz0`,
  where the composition is checked up to definitional equality.
  The rest is the source proof: Mathlib's
  `ZMod.intCast_zmod_eq_zero_iff_dvd` gives `m = n * k`; the witness is
  `⟨Int.castRingHom ZHat k, intToProCInteger_mem_localBaseValuation_range K k⟩`
  (M163.008), and `Subtype.ext`, `map_nsmul`, the integer identity
  `n • k = m` (by `simpa [nsmul_eq_mul]`) and `hm` show `n • w = z`.
- `nZ ≤ ker`: an element `n • w` with `w ∈ Z` reduces to
  `zHatReduction n hn (n • (w : ℤ̂))`; `map_nsmul` turns this into
  `n • zHatReduction n hn w`, which `simp [nsmul_eq_mul]` shows is `0` in
  `ZMod n`, since `(n : ZMod n) = 0`.

### `localCanonicalValueQuotientMap_bijective` (M163.013)

`canonicalValueQuotientMap Z n hn : Z ⧸ nsmulWithin Z n →+ ZMod n` is the lift
of `valueGroupReduction Z n hn`, which is definitionally
`localValueGroupReduction K n hn`.

- Injective: for classes of `z₁` and `z₂` (by `Quotient.inductionOn'`) with
  equal images, `QuotientAddGroup.eq_iff_sub_mem` reduces the goal to
  `z₁ - z₂ ∈ nsmulWithin Z n`. Rewriting with
  `← localValueGroupReduction_ker K n hn` (M163.011 above), the goal becomes
  `localValueGroupReduction K n hn (z₁ - z₂) = 0`, which `map_sub`, the
  hypothesis (changed to equality of the two reductions) and `sub_self`
  prove.
- Surjective: for `a : ZMod n`, M163.010 above gives `z : Z` reducing to `a`,
  and the class `QuotientAddGroup.mk' (nsmulWithin Z n) z` maps to `a`
  definitionally (`exact hz`).

These are the source proofs unchanged after the `intro`.

## Simp attributes

The source marks M163.004 and M163.006 `@[simp]`. On a closed theorem, whose
type is a constant `…Statement`, the attribute would not give a usable simp
lemma, so the exact theorems carry no attribute. Instead, after each of them
the module adds a wrapper with the explicit source telescope and the source
equation as its type, marked `@[simp]` and proved by applying the exact
theorem:

- `baseFieldUnitsEquiv_val_apply (K : Type) [Field K] (x : Kˣ)`, proved by
  `baseFieldUnitsEquiv_val K x`;
- `localBaseValuation_baseFieldUnitsEquiv_apply (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (x : Additive Kˣ)`, proved by `localBaseValuation_baseFieldUnitsEquiv K x`.

Their types are the bodies of the two targets after the binders. They are
not second copies under the adapted names; their only role is to restore the
source simp behaviour. No proof in this module uses them.

## Published declarations used

- The seven targets, from the [statement module](Statements.md), and
  through it `baseFieldUnitsEquiv`, `localBaseValuation` and
  `localValueGroupReduction` ([definitions](../U001/Definitions.md)),
  `nsmulWithin`, `valueGroupReduction` and `canonicalValueQuotientMap`
  ([M025 definitions](../../../../../AbstractClassFieldTheory/Degree/Valuation/Definitions.md)),
  `ZHat` and `zHatReduction`
  ([ProfiniteIntegerCore](../../../../../../GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Definitions.md))
  and `valuationMap`
  ([M134.002](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence/Definitions.md)).
- `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val`
  (M096.002, [proof](../../SeparableUnitsNorm/BaseUnits/U002/Proofs.md)), in
  M163.004.
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective`
  (M134.005, [proof](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence/U005/Proofs.md)),
  in M163.007, at `K : Type`.
- `Langlands.NYLL.ClassFormation.zHatReduction_int` (M009.007,
  [proof](../../../../../../GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U007/Proofs.md)),
  in M163.010 and M163.011. Its target is the reducible alias of the
  M008.019 target `zHatReduction_intCastStatement n hn m`, the equation
  `zHatReduction n hn (m : ZHat) = (m : ZMod n)`.
- From Lean core and Mathlib: `le_antisymm`, `ZMod.intCast_surjective`,
  `ZMod.intCast_zmod_eq_zero_iff_dvd`, `map_nsmul`, `map_sub`, `nsmul_eq_mul`,
  `sub_self`, `Subtype.ext`, `Quotient.inductionOn'`,
  `QuotientAddGroup.eq_iff_sub_mem`, `QuotientAddGroup.mk'`, the simp set
  used by the two `simp` calls, and the instance
  `IsSepClosure.isGalois : IsGalois K (SeparableClosure K)`.

The imports are the statement module and the three proof modules above:
`...SeparableUnitsNorm.BaseUnits.U002.Proofs`,
`...ValuationExactSequence.U005.Proofs` and
`...ProfiniteInteger.U007.Proofs`.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`, with SHA-256
`1cd6d5fb117831219fac27dbb60cc7c3d7d866ad78fc4f771acdf694d3aa3ad9`. The
namespace and opens are at lines 21–26, the `noncomputable section` at line
30 and the section variables at lines 32–33.

| Unit | Original theorem (lines, docstring to end of proof) | Theorem here |
| --- | --- | --- |
| M163.004 | `baseFieldUnitsEquiv_val` (49–63, `omit`, `@[simp]`) | `baseFieldUnitsEquiv_val` |
| M163.006 | `localBaseValuation_baseFieldUnitsEquiv` (73–79, `@[simp]`) | `localBaseValuation_baseFieldUnitsEquiv` |
| M163.007 | `localBaseValuation_range` (81–95) | `localBaseValuation_range` |
| M163.008 | `intToProCInteger_mem_localBaseValuation_range` (97–102) | `intToProCInteger_mem_localBaseValuation_range` |
| M163.010 | `localValueGroupReduction_surjective` (110–119) | `localValueGroupReduction_surjective` |
| M163.011 | `localValueGroupReduction_ker` (121–154) | `localValueGroupReduction_ker` |
| M163.013 | `localCanonicalValueQuotientMap_bijective` (167–189) | `localCanonicalValueQuotientMap_bijective` |

Worker 120 made these changes on 15 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and kept the source
  `open` lines;
- stated each theorem as the published closed target and began each proof
  with `intro` of the section variables and the theorem's binders. In
  M163.010 the source's `intro a` is merged into this `intro`;
- kept the source proof scripts, except the M163.011 step with
  `zHatReduction_int` described above;
- did not put the `@[simp]` attributes of M163.004 and M163.006 on the closed
  theorems, and added the two `_apply` wrappers instead;
- kept the source docstrings of the seven theorems, added docstrings for the
  wrappers and a module docstring, and omitted the `noncomputable section`
  and all other source declarations (M163.001–M163.003, M163.005, M163.009,
  which are published as definitions, and M163.012, a later definition
  unit);
- replaced the source imports by the published modules above.

Worker 85's private development probe (task context) had already replayed
these proofs, including the same M163.011 replacement; this module was
written and checked independently from the original source. No other draft
was used.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`, compiled this module
with no errors or warnings. Inspection of `baseFieldUnitsEquiv_val` and of
`localCanonicalValueQuotientMap_bijective` (whose proof uses M163.006,
M163.007, M163.008, M163.010 and M163.011) reported theorems with no level
parameters using only the axioms `propext`, `Classical.choice` and
`Quot.sound`. These development checks are not independent acceptance.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
in the Library.
