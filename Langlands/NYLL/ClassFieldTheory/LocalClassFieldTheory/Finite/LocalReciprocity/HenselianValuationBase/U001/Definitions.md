# The base value group of a local field in `ℤ̂` (M163.001–M163.003, M163.005, M163.009)

Let `K` be a nonarchimedean local field (a field `K : Type` with
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances), `K^sep = SeparableClosure K` Mathlib's absolute separable closure
and `G = Gal(K^sep / K)` its absolute separable Galois group. Finite local
reciprocity treats `G` as the group of an abstract class formation whose
coefficient module is `(K^sep)ˣ`, written additively, and whose "base field"
is the whole group `G`. This module defines three declarations and reuses two existing constructions:

- `intrinsicAbsoluteGalois K` (M091.001) supplies source unit M163.001,
  the private abbreviation `G`, with its exact body `Gal(SeparableClosure K / K)`.
- `intrinsicAbsoluteUnits K` (M091.002) supplies source unit M163.002,
  the private abbreviation `A`, with its exact body
  `galoisAmbientUnitsRep K (SeparableClosure K)`.
- `baseFieldUnitsEquiv K` (M163.003) identifies `Additive Kˣ` with the
  elements of that coefficient module fixed by the base subgroup `G` itself.
- `localBaseValuation K` (M163.005) is NYLL's integer valuation of `K`, read
  on that fixed subgroup and cast into the profinite integers `ℤ̂`.
- `localValueGroupReduction K n hn` (M163.009) is the reduction modulo `n`
  of the range of `localBaseValuation K`.

All five names are in the namespace `Langlands.NYLL.LocalClassFieldTheory`,
with the last three retaining their source names.

**Sign convention.** NYLL's integer valuation
`valuationMap K : Additive Kˣ →+ ℤ` is the *negative* of the usual normalized
discrete order `ord` (with `ord(π) = 1` for a prime element `π` of the
valuation ring `𝒪[K]`): writing `v(x) = valuationMap K (Additive.ofMul x)`,
we have `v(x) = -ord(x)`. It is built from Mathlib's
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`, an order-preserving
isomorphism onto `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, so elements of
valuation less than one get negative integers. The source proves that a
prime element of `𝒪[K]` has `v = -1` and its inverse has `v = 1`
(`v_integerRingIrreducibleFieldUnit` and
`v_integerRingIrreducibleFieldUnit_inv`, original `IdealQuotients.lean`,
lines 210–244). The published audit
`notes/reuse/nyll-finite-local-reciprocity-audit.md` (section 2.3) records
the same convention, as does the published Markdown of
`...ValuationExactSequence.U027.Definitions`.

Consequently `localBaseValuation K` sends the fixed element corresponding to a
prime element `π` of `𝒪[K]` to `-1` in `ℤ̂`, not to `1`. The source
docstring of `localBaseValuation` ("The normalized valuation
`v_K : Kˣ → ℤ`, embedded in `ℤ̂`") is kept verbatim; under NYLL's
convention the integer valuation it refers to is `v = -ord`. The range of
`localBaseValuation K`, and hence the domain of `localValueGroupReduction`,
does not depend on the sign, because negation maps the image of `ℤ` in `ℤ̂`
onto itself.

## The Lean definitions

```lean
namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory
open LocalFieldTheory
open ClassFormation

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

def baseFieldUnitsEquiv :
    Additive Kˣ ≃+ ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K)) :=
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K))
        (closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K))))

def localBaseValuation :
    ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K)) →+ ZHat :=
  (Int.castRingHom ZHat).toAddMonoidHom.comp
    ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K).comp
      (baseFieldUnitsEquiv K).symm.toAddMonoidHom)

def localValueGroupReduction (n : ℕ) (hn : 0 < n) :
    (localBaseValuation K).range →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp
    (localBaseValuation K).range.subtype

end
end Langlands.NYLL.LocalClassFieldTheory
```

The docstrings are omitted from this display; the Lean file has them.

## The objects involved

All names below are published in the Library or in Mathlib.

- `SeparableClosure K` is Mathlib's absolute separable closure of `K`, the
  abbreviation `separableClosure K (AlgebraicClosure K)` for the separable
  closure of `K` inside `AlgebraicClosure K`. Instance synthesis finds that it
  is Galois over `K` through Mathlib's
  `separableClosure.isGalois K (AlgebraicClosure K)` (and a separable closure
  through `separableClosure.isSepClosure K (AlgebraicClosure K)`); the
  abbreviation and both instances come from `Mathlib.FieldTheory.IsSepClosed`.
- `intrinsicAbsoluteGalois F` and `intrinsicAbsoluteUnits F` (M091.001,
  M091.002, namespace `Langlands.NYLL.LocalClassFieldTheory`, module
  `...LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`) are, for
  `(F : Type) [Field F]`, the abbreviations
  `intrinsicAbsoluteGalois F := Gal(SeparableClosure F / F)` and
  `intrinsicAbsoluteUnits F : Rep ℤ (intrinsicAbsoluteGalois F) :=
  galoisAmbientUnitsRep F (SeparableClosure F)`.
- `galoisAmbientUnitsRep K Ω` (M088.001, module
  `...LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions`) is the
  abbreviation `Rep.ofAlgebraAutOnUnits K Ω`: Mathlib's `ℤ`-linear
  representation of `Ω ≃ₐ[K] Ω = Gal(Ω / K)` on `Additive Ωˣ` given by the
  natural action of automorphisms on units.
- `ambientFixedAddSubgroup A H` (M023.001, namespace
  `Langlands.NYLL.KummerTheory`, module
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`)
  is, for a representation `A : Rep ℤ G` and a closed subgroup `H` of `G`,
  the additive subgroup `{a | ∀ h ∈ H, A.ρ h a = a}` of the elements of `A`
  fixed by `H`.
- `baseField G` (M010.003, namespace `Langlands.NYLL.ClassFormation`, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`)
  is the closed subgroup `⊤` of a group `G` with a topology, the subgroup
  that represents the base field in an abstract class formation.
- `closedFixingSubgroup K Ω E` (M087.001, module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`)
  is the fixing subgroup of an intermediate field `E` of a Galois extension
  `Ω / K`, as a closed subgroup of `Gal(Ω / K)`.
- `baseUnitsEquivGaloisAmbientFixed K Ω` (M096.001, module
  `...LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions`) is, for a
  Galois extension `Ω / K`, an additive equivalence from `Additive Kˣ` to
  `ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
  (closedFixingSubgroup K Ω ⊥)`. Its body identifies `Kˣ` with the units of
  the bottom intermediate field `⊥` (Mathlib's `IntermediateField.botEquiv`)
  and then applies the published `intermediateFieldUnitsEquivGaloisFixed`
  (whose published target `intermediateFieldUnitsEquivGaloisFixed_coeStatement`
  says that it sends a unit of `⊥` to its image in `Ωˣ`).
- `closedFixingSubgroup_bot_eq_baseField K Ω` (M089.001, module
  `...LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`) proves
  `closedFixingSubgroup_bot_eq_baseFieldStatement K Ω`, that is,
  `closedFixingSubgroup K Ω ⊥ = baseField (Gal(Ω / K))`.
- `valuationMap K` (M134.002,
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`,
  module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`)
  is NYLL's integer valuation `Additive Kˣ →+ ℤ`, the negative of the usual
  normalized order (see the sign convention above).
- `ZHat` (M008.008, namespace `Langlands.NYLL.ClassFormation`, module
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`)
  is NYLL's model of the profinite integers `ℤ̂ = lim ℤ/nℤ`, with its
  published commutative ring structure (instance
  `Langlands.NYLL.PortInternal.M008.d009`). `Int.castRingHom ZHat` is
  Mathlib's ring homomorphism `ℤ →+* ℤ̂`.
- `zHatReduction n hn` (M008.018, same module) is the continuous additive
  reduction `ℤ̂ → ZMod n` for `0 < n`.

## The construction

**M163.001, M163.002.** The published abbreviations
`intrinsicAbsoluteGalois K` and `intrinsicAbsoluteUnits K` have exactly the
source bodies of `G K` and `A K`. The definitions below use these existing
names directly. The duplicate port-internal aliases from the submitted version
were removed during integration; this changes neither the types nor the values
of the three public definitions.

**M163.003.** `baseFieldUnitsEquiv K` is the composite of two additive
equivalences:

1. `baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)`, from
   `Additive Kˣ` to the subgroup of `Additive (K^sep)ˣ` fixed by
   `closedFixingSubgroup K (SeparableClosure K) ⊥`;
2. `AddEquiv.addSubgroupCongr h`, Mathlib's equivalence between two equal
   additive subgroups, for the equality
   `h : ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (closedFixingSubgroup K K^sep ⊥) =
   ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K))` obtained by
   applying `congrArg (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K))` to the published
   theorem `closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)`.

The instance `IsGalois K (SeparableClosure K)` needed by step 1 and by
`closedFixingSubgroup` is Mathlib's `separableClosure.isGalois`. The second step changes only the name of the subgroup,
not its elements. So `baseFieldUnitsEquiv K` maps `Additive.ofMul x` to the
element of the fixed subgroup given by step 1. The source states in the
theorem `baseFieldUnitsEquiv_val` (M163.004, not part of this module) that its
underlying element of `SeparableClosure K` is
`algebraMap K (SeparableClosure K) x`; the source proves this from
`baseUnitsEquivGaloisAmbientFixed_val` (M096.002), whose target
`baseUnitsEquivGaloisAmbientFixed_valStatement` is published.

**M163.005.** `localBaseValuation K` is the composite of three additive
homomorphisms: the inverse of `baseFieldUnitsEquiv K`, then
`valuationMap K : Additive Kˣ →+ ℤ`, then the cast `ℤ → ℤ̂`. Hence, for
`x : Kˣ`, the value of `localBaseValuation K` at
`baseFieldUnitsEquiv K (Additive.ofMul x)` is the image in `ℤ̂` of the
integer `v(x) = -ord(x)`. The source states this as the theorem
`localBaseValuation_baseFieldUnitsEquiv` (M163.006, proved by `simp`) and
proves in `localBaseValuation_range` (M163.007) that the range of
`localBaseValuation K` is the image of `ℤ` in `ℤ̂`; neither theorem is part of
this module.

**M163.009.** `localValueGroupReduction K n hn` is the composite of the
inclusion of the range `(localBaseValuation K).range` (an additive subgroup of
`ℤ̂`) into `ℤ̂` and the reduction `zHatReduction n hn : ℤ̂ → ZMod n`, viewed as
an additive monoid homomorphism. The positivity hypothesis `hn` is passed to
`zHatReduction`.

Each of the three new declarations has a term body and uses no tactics.

## Binders and universes

The three new declarations use the source section variables
`(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`; Lean includes only those that a declaration
uses. `baseFieldUnitsEquiv` and the two reused intrinsic abbreviations take
only `(K : Type) [Field K]`, while `localBaseValuation` and
`localValueGroupReduction` take all four instance binders (they use
`valuationMap K`). `localValueGroupReduction` also takes the explicit
`(n : ℕ) (hn : 0 < n)`. `K` lives in `Type`, as in the source; no declaration
has universe parameters.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean),
SHA-256 `1cd6d5fb117831219fac27dbb60cc7c3d7d866ad78fc4f771acdf694d3aa3ad9`.
The relevant lines are:

- lines 21–33: `namespace LocalClassFieldTheory`,
  `open RamificationTheory KummerTheory`, `open LocalFieldTheory`,
  `open ClassFormation`, `noncomputable section` and the `variable` line for
  `K`;
- M163.001: the private abbreviation `G` at line 35;
- M163.002: the private abbreviation `A` at lines 37–38;
- M163.003: docstring at lines 40–41, definition and body at lines 42–47;
- M163.005: docstring at lines 65–66, definition and body at lines 67–71;
- M163.009: docstring at line 104, definition and body at lines 105–108.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.G` (M163.001, private abbrev) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` (published, reused directly) |
| `LocalClassFieldTheory.A` (M163.002, private abbrev) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteUnits` (published, reused directly) |
| `LocalClassFieldTheory.intrinsicAbsoluteGalois` (M091.001, reused for M163.001) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` (published) |
| `LocalClassFieldTheory.intrinsicAbsoluteUnits` (M091.002, reused for M163.002) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteUnits` (published) |
| `LocalClassFieldTheory.baseFieldUnitsEquiv` (M163.003) | `Langlands.NYLL.LocalClassFieldTheory.baseFieldUnitsEquiv` (this module) |
| `LocalClassFieldTheory.localBaseValuation` (M163.005) | `Langlands.NYLL.LocalClassFieldTheory.localBaseValuation` (this module) |
| `LocalClassFieldTheory.localValueGroupReduction` (M163.009) | `Langlands.NYLL.LocalClassFieldTheory.localValueGroupReduction` (this module) |
| `LocalClassFieldTheory.galoisAmbientUnitsRep` (M088.001, used) | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` (published) |
| `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` (M096.001, used) | `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` (published) |
| `LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField` (M089.001, used) | `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField` (published proof of `closedFixingSubgroup_bot_eq_baseFieldStatement`) |
| `KummerTheory.ambientFixedAddSubgroup` (M023.001, used) | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (published) |
| `ClassFormation.baseField` (M010.003, used) | `Langlands.NYLL.ClassFormation.baseField` (published) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` (M134.002, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` (published) |
| `ClassFormation.ZHat` (M008.008, used) | `Langlands.NYLL.ClassFormation.ZHat` (published) |
| `ClassFormation.zHatReduction` (M008.018, used) | `Langlands.NYLL.ClassFormation.zHatReduction` (published) |

Rows M163.001, M163.002, M163.003, M163.005 and M163.009 of the published
partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserve the original port names and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase`.
Integration maps M163.001 and M163.002 directly to the existing M091 names
above. The other three names were absent from the reviewed Library base. (The
Library's `Langlands.Correspondence.baseFieldUnitsEquiv`, in
`Langlands/Correspondence/RankOneEpsilonCharacterTransport.lean`, is an
unrelated declaration in another namespace.)

**Reuse of published constructions.** The source bodies of the private
abbreviations `G` and `A` coincide with the published abbreviations
`intrinsicAbsoluteGalois` and `intrinsicAbsoluteUnits` (M091.001, M091.002,
from the source file `IntrinsicAbsoluteData.lean`, lines 27–37), with the same
`(F : Type) [Field F]` parameters. The port therefore does not repeat those
constructions: the source names `G` and `A` are replaced directly by the
published intrinsic names. The three
public definitions M163.003, M163.005 and M163.009 have no published
counterpart: the Library's `Langlands.Correspondence.baseFieldUnitsEquiv`
has a different (topological, multiplicative) type, and no published
declaration transports `valuationMap` to the fixed coefficient group or
reduces its range modulo `n`.

## Imports and modification record

The direct imports are:

- `Mathlib.FieldTheory.IsSepClosed`, for `SeparableClosure` and its
  Galois instance;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`
  (M091.001, M091.002: `intrinsicAbsoluteGalois`, `intrinsicAbsoluteUnits`);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions`
  (M096.001, which imports `galoisAmbientUnitsRep`,
  `ambientFixedAddSubgroup` and `closedFixingSubgroup`);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`
  (M089.001, which imports `baseField`);
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`
  (`valuationMap`);
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`
  (`ZHat`, its ring structure and `zHatReduction`).

They replace the source's three NYLL imports (`GaloisExtensionQuotient`,
`SeparableUnitsNorm` and
`ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation`),
which serve the other declarations of the source file. Every transitive import
lies in the approved Mathlib environment or the published Library.

Worker 85 extracted these five source units on 15 November 2026. Integrator
then consolidated the two duplicate aliases. The Lean header records the changes:

- the private source abbreviations `G` and `A` are replaced by the published
  `intrinsicAbsoluteGalois` and `intrinsicAbsoluteUnits`, with exactly the same
  bodies and parameters;
- M163.003, M163.005 and M163.009 are in the namespace
  `Langlands.NYLL.LocalClassFieldTheory`, with the source opens
  (`RamificationTheory`, `KummerTheory`, `LocalFieldTheory`, `ClassFormation`).
  Their docstrings, types and bodies are unchanged except for the direct reuse
  of the intrinsic names in place of `G` and `A`;
- the imports are replaced as described above.

Every other source declaration is omitted. In particular the theorems
M163.004, M163.006–M163.008, M163.010, M163.011 and M163.013 and the
definition M163.012 (`localValueGroupQuotientEquivZMod`, which uses the
theorem M163.011) are not part of this module. No theorem, instance or
notation or alias is introduced.

## Checks

The submitted version, including the two subsequently consolidated aliases,
compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against Library commit
`7229bb456a9afe1fc799771f6516c4b5dc9f976b`. Its inspection reported all five
declarations as definitions without level parameters, with the binders listed
above, depending only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

A private development probe, not part of this module, compiled the source
proofs of M163.006, M163.007, M163.008 and M163.010 against this module, with
the source theorem names replaced by probe names and with the published
`valuationMap_surjective` and `zHatReduction_int`. These development checks
are not independent acceptance.

## Use downstream

In the source, these definitions feed the rest of the file: the evaluation
lemmas M163.004 and M163.006, the range computation M163.007–M163.008, the
surjectivity and kernel of the reduction (M163.010, M163.011), the quotient
equivalence M163.012 and M163.013. Through them they feed the local
henselian valuation `localHenselianValuation` (M253) used by the NormResidue
closure.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted these units directly from the
pinned original; no other project worker supplied code.
