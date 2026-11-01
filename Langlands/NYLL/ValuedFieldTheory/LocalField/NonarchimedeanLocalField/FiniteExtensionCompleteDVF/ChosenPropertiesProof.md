# Properties of the chosen complete discrete valuation on a finite local extension: proof

This module proves the closed proposition
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionPropertiesStatement`
(NYLL M248.007, M248.009 and M248.010), published in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesStatement`.
The proof adapts the proofs of three theorems from Naganori Yamaguchi's
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`:

- M248.007, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasExtension`,
  [lines 140–150](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L140-L150);
- M248.009, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_isIntegralClosure`,
  [lines 163–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L163-L174);
- M248.010,
  `LocalFieldTheory.chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite`,
  [lines 176–192](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L176-L192).

| Theorem | Universe parameters | Complete unapplied type |
| --- | --- | --- |
| `Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_properties` | none | `ChosenLocalExtensionPropertiesStatement` |

The theorem's type is the named target constant itself, with no arguments and
no universe parameters. The module contains no other declaration and no
instance.

## The target

The target quantifies over

```
(K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

and concludes

```
∃ hExt : _root_.Valuation.HasExtension
    (localCompleteDVF K).valuation
    (chosenLocalExtensionCompleteDVF K L).valuation,
  letI : _root_.Valuation.HasExtension
      (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation := hExt
  IsIntegralClosure
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
      (localCompleteDVF K).valuation.valuationSubring L ∧
    Module.Finite
      (localCompleteDVF K).valuation.valuationSubring
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
```

Here `localCompleteDVF K` is the published canonical complete discrete
valuation of `K` (adapted M248.001), and `chosenLocalExtensionCompleteDVF K L`
is the published chosen complete discrete valuation on `L` (adapted M248.006).
Write `K₀` for the canonical valuation subring of `K` and `L₀` for the chosen
valuation subring of `L`. The target's Markdown explains its scalar
structures:

- In the integral-closure conjunct, the algebra `L₀ → L` is the actual
  inclusion, and the algebra `K₀ → L` is `Algebra.ofSubsemiring` of the
  supplied `Algebra K L`: the inclusion into `K` followed by the supplied
  `algebraMap K L`. This conjunct does not mention `hExt`.
- In the finiteness conjunct, the module structure of `L₀` over `K₀` comes
  from Mathlib's `Valuation.HasExtension.instAlgebra_valuationSubring` at
  `hExt`. Its algebra map sends `a` to the element of `L₀` whose image in `L`
  is `algebraMap K L (a : K)`.

Both carriers are in `Type 0`. No structure is placed on `L` beyond its field
structure and the supplied algebra. The identity extension `L = K` is one of
the cases covered.

## The proof

The published definition `chosenLocalExtensionCompleteDVF K L` is
`Classical.choose` applied to the published existence theorem
`exists_integralClosure_standard_completeDVF_extension.{0, 0, 0} K L (localCompleteDVF K)`.
That theorem (adapted M245.018, module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof`)
proves `ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u, v, w}`.
At universes `0, 0, 0` and base `localCompleteDVF K`, it states that there is
some `target : CompleteDVF.{0, 0} L` with a witness
`hExt : Valuation.HasExtension (localCompleteDVF K).valuation target.valuation`
such that, with `hExt` installed, `target.valuation.valuationSubring` is an
integral closure of `K₀` in `L`.

The proof (Lean file, lines 43–60) runs as follows.

1. `intro K L _ _ _ _ _ _ _ _` introduces the two fields and the eight
   instance arguments in target order.
2. `have hChosen := Classical.choose_spec (exists_integralClosure_standard_completeDVF_extension.{0, 0, 0} K L (localCompleteDVF K))`.
   `hChosen` is the property of the chosen target: an existential over
   `HasExtension` witnesses, followed by the integral-closure property. Its
   statement mentions the target as `Classical.choose (…)`. That term is the
   value of `chosenLocalExtensionCompleteDVF K L`. Lean accepts the target in
   either spelling in the next two steps by unfolding the definition. The
   definition's body cites the existence theorem through an auxiliary proof
   constant, and any two proofs of the same proposition are definitionally
   equal.
3. `let hExt : Valuation.HasExtension (localCompleteDVF K).valuation (chosenLocalExtensionCompleteDVF K L).valuation := Classical.choose hChosen`.
   This is the M248.007 conclusion, obtained as in the source
   (`Classical.choose (Classical.choose_spec …)`). Because `hExt` is a local
   variable whose type is a class, Lean uses it as a local instance in the
   rest of the proof. Nothing is declared globally.
4. `have hIntegralClosure : IsIntegralClosure L₀ K₀ L := Classical.choose_spec hChosen`.
   This is the M248.009 conclusion, obtained as in the source
   (`Classical.choose_spec (Classical.choose_spec …)`). The `letI` binding in
   `hChosen` does not change the proposition, since the integral-closure
   property does not use the witness. `hIntegralClosure` is also a local
   instance from here on.
5. `exact ⟨hExt, hIntegralClosure, IsIntegralClosure.finite K₀ K L L₀⟩`
   provides the existential witness `hExt` and then the two conjuncts. After
   the witness is supplied, the `letI` in the target binds `hExt` itself, so
   the conjuncts' scalar structures are those built from the same witness.
   The last component is the M248.010 conclusion, obtained exactly as in the
   source.

### The finiteness step

Mathlib's `IsIntegralClosure.finite A K L C`
(`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`, lines 172–178,
with ambient hypotheses at lines 43–58, 87 and 147) proves `Module.Finite A C`
when `K` is the fraction field of an integrally closed Noetherian domain `A`,
`L` is a finite separable extension of `K`, and `C` is an integral closure of
`A` in `L` with compatible scalar towers. Here `A = K₀` and `C = L₀`. Lean's
instance search supplied the hypotheses as follows; a private check printed
each one (see below).

- `IsFractionRing K₀ K`: Mathlib's `ValuationSubring` instance
  `ValuationSubring.instIsFractionRingSubtypeMem`.
- `IsIntegrallyClosed K₀`: Mathlib's valuation-subring instance
  `instIsIntegrallyClosedSubtypeMemValuationSubring`
  (`Mathlib/RingTheory/Valuation/LocalSubring.lean`, line 38).
- `IsNoetherianRing K₀`: through `IsPrincipalIdealRing.isDedekindDomain`.
  The principal-ideal property comes from Mathlib's instance
  `Valuation.valuationSubring_isDiscreteValuationRing`
  (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`, line 449). Its
  value-group hypotheses come from the rank-one-discreteness instance
  `IsCompleteDiscrete.isRankOneDiscrete`, which is stored in the
  `CompleteDVF` bundle `localCompleteDVF K`.
- `Algebra K L`, `FiniteDimensional K L`, `Algebra.IsSeparable K L`: the
  supplied instances.
- `Algebra K₀ L`: `Algebra.ofSubsemiring` of the supplied `Algebra K L`, the
  same algebra as in the target's integral-closure conjunct.
- `IsScalarTower K₀ K L`: Mathlib's
  `Valuation.HasExtension.instIsScalarTower_valuationSubring`
  (`Mathlib/RingTheory/Valuation/Extension.lean`, line 189), which does not
  use the witness.
- `Algebra L₀ L`: the `ValuationSubring` inclusion algebra.
- `IsIntegralClosure L₀ K₀ L`: the local instance `hIntegralClosure`.
- `Algebra K₀ L₀`: `Valuation.HasExtension.instAlgebra_valuationSubring`
  (Extension.lean, line 182) at the local witness `hExt`.
- `IsScalarTower K₀ L₀ L`:
  `Valuation.HasExtension.instIsScalarTower_valuationSubring'`
  (Extension.lean, line 192) at `hExt`.

So the resulting `Module.Finite K₀ L₀` uses the module structure
`Algebra.toModule` of `instAlgebra_valuationSubring` at `hExt`. This is the
module structure in the target's finiteness conjunct.

Mathematically: the chosen valuation was chosen so that it extends the
canonical valuation of `K` and its valuation ring is the integral closure of
the canonical valuation ring `K₀` in `L`. The ring `K₀` is a discrete
valuation ring, hence integrally closed and Noetherian, with fraction field
`K`. Since `L/K` is finite and separable, the integral closure of `K₀` in `L`
is a finite `K₀`-module.

The proof uses no uniqueness or comparison of valuation extensions, no
canonical integer-ring comparison, no fundamental identity and no reciprocity
result. It declares no global instance.

## Source correspondence and modifications

| Source unit | Source declaration (lines) | In this proof |
| --- | --- | --- |
| M248.005 | private `chosenLocalExtensionCompleteDVF_exists` (114–128) | not used; `Classical.choose_spec` is applied to the published existence theorem that defines the published M248.006 choice |
| M248.007 | `chosenLocalExtensionCompleteDVF_hasExtension` (140–150) | step 3, `Classical.choose hChosen`, giving the existential witness |
| M248.008 | `chosenLocalExtensionCompleteDVF.instHasExtension` (152–161) | omitted; the witness is the local variable `hExt`, used as a local instance |
| M248.009 | `chosenLocalExtensionCompleteDVF_isIntegralClosure` (163–174) | step 4, `Classical.choose_spec hChosen`, the first conjunct |
| M248.010 | `chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite` (176–192) | step 5, `IsIntegralClosure.finite K₀ K L L₀`, the second conjunct |

The source proofs are:

```
-- M248.007, lines 149–150
  Classical.choose
    (Classical.choose_spec (chosenLocalExtensionCompleteDVF_exists K L))
-- M248.009, lines 173–174
  Classical.choose_spec
    (Classical.choose_spec (chosenLocalExtensionCompleteDVF_exists K L))
-- M248.010, lines 186–192
  let : IsIntegralClosure
      (chosenLocalExtensionCompleteDVF K L).valuationSubring
      (localCompleteDVF K).valuationSubring L :=
    chosenLocalExtensionCompleteDVF_isIntegralClosure K L
  exact IsIntegralClosure.finite
    (localCompleteDVF K).valuationSubring K L
    (chosenLocalExtensionCompleteDVF K L).valuationSubring
```

The adapted proof makes only these changes:

- **One theorem.** The three source theorems become one theorem whose type is
  the closed target. Their shared binders are introduced by `intro`, and the
  three conclusions are assembled with one anonymous constructor.
- **Existence input.** The source applies `Classical.choose_spec` to its
  private M248.005 wrapper. That wrapper extracts the existence part of the
  source's `exists_integralClosure_standard_fundamental_identity`. Here
  `Classical.choose_spec` is applied directly to the published existence
  theorem `exists_integralClosure_standard_completeDVF_extension` at
  universes `0, 0, 0` and base `localCompleteDVF K`. That application is the
  one in the body of the published M248.006 definition. The resulting
  property `hChosen` has the same form as the property the source obtains
  from M248.005 by its first `Classical.choose_spec`, up to the
  `valuationSubring` abbreviation.
- **Witness.** The M248.008 global instance is not declared. In M248.010 the
  source gets the module structure from that instance. Here it comes from the
  local variable `hExt` of step 3, which is also the existential witness of
  the target.
- **Spelling.** The valuation subrings are written
  `….valuation.valuationSubring`, which is what the source's
  `CompleteDVF.valuationSubring` abbreviation unfolds to, as in the target.
  `HasExtension` is written in prefix form with `_root_.`.
- **Namespace, name and imports.** The namespace is prefixed with
  `Langlands.NYLL`. The task's suggested name
  `chosenLocalExtension_properties` replaces the three theorem names. The
  original imports are replaced by the published statement module and
  `Mathlib.RingTheory.DedekindDomain.IntegralClosure`, which supplies
  `IsIntegralClosure.finite` and the principal-ideal-to-Dedekind instance
  chain. The statement module brings in the published `Chosen` module and,
  through it, the published existence theorem.

The following remain outside this proof: M248.011, uniqueness of the
valuation extension; comparison of the chosen valuation or target with an
independently supplied one; the canonical integer-ring comparisons M248.003
and M248.004; the fundamental identity for the chosen target; and the host
inertia and finite `Type 0` reciprocity results.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a theorem with no level parameters. It depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The
published target pair `ChosenPropertiesStatement.lean`/`.md` and its imports
are unchanged.

A separate private check module, not submitted, did the following:

- It compared the declaration's type with the constant
  `ChosenLocalExtensionPropertiesStatement` as Lean expressions and found
  them equal, with no level parameters.
- It printed the instances found for `IsFractionRing K₀ K`,
  `IsIntegrallyClosed K₀`, `IsNoetherianRing K₀`, `IsPrincipalIdealRing K₀`,
  `IsDiscreteValuationRing K₀`, `Algebra K₀ L` and `IsScalarTower K₀ K L`,
  and, under a `HasExtension` witness, for `Algebra K₀ L₀`,
  `IsScalarTower K₀ L₀ L` and `Algebra L₀ L`. They are the ones listed above.
- It checked by `rfl` that `chosenLocalExtensionCompleteDVF K L` equals
  `Classical.choose` of the published existence theorem at `K`, `L` and
  `localCompleteDVF K`.

These checks establish compilation and the correspondence stated here.
Exact-target validation, semantic review and publication are separate steps.

## Attribution

The complete 206-line original was read. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source partition `notes/reuse/nyll-public-port/m241-m258.md` records no
patch10 compatibility edit for M248. No applicable source erratum was found in
the checked project and Library notes on 31 October 2026.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The Lean
file states its modifications in a comment after the header. The source is
Apache-2.0. The inherited, unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values
are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE has no entry for the selected source file.

The source uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This adaptation uses the approved
environment above.

On 31 October 2026, Worker 785 adapted the three proofs with the changes
listed above and wrote this explanation. Worker 106 supplied routing only. The
published inputs (the target statement, `localCompleteDVF`,
`chosenLocalExtensionCompleteDVF` and the existence theorem, all adapted by
Worker 785) are imported by Lean name. No unpublished implementation or draft
from another worker was reused.
