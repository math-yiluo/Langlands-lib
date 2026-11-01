# Properties of the chosen complete discrete valuation on a finite local extension: statement

This module adapts the statements of three theorems from Naganori Yamaguchi's
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`:

- M248.007, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasExtension`,
  [lines 140–150](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L140-L150);
- M248.009, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_isIntegralClosure`,
  [lines 163–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L163-L174);
- M248.010,
  `LocalFieldTheory.chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite`,
  [lines 176–192](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L176-L192).

The module contains one closed proposition,
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionPropertiesStatement : Prop`,
in module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesStatement`.
It is a `Prop`-valued `def` with no universe parameters and no arguments. It
is a statement only. The module contains no proof, no instance and no other
declaration.

| Original | Adapted |
| --- | --- |
| `theorem chosenLocalExtensionCompleteDVF_hasExtension` (M248.007, lines 140–150) | the existential `∃ hExt : …` (statement only) |
| `instance chosenLocalExtensionCompleteDVF.instHasExtension` (M248.008, lines 152–161) | no declaration; replaced by `letI : … := hExt` inside the proposition |
| `theorem chosenLocalExtensionCompleteDVF_isIntegralClosure` (M248.009, lines 163–174) | the first conjunct, `IsIntegralClosure …` (statement only) |
| `theorem chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite` (M248.010, lines 176–192) | the second conjunct, `Module.Finite …` (statement only) |

## Statement

The proposition quantifies over the complete source telescope, which is the
same for all three source theorems and for the published chosen definition:

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

The two names are published Library declarations, used unchanged:

- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K : CompleteDVF.{0,0} K`
  (adapted M248.001, module `…FiniteExtensionCompleteDVF.Canonical`) is the
  canonical complete discrete valuation of `K`. Its valuation is the
  canonical `ValuativeRel.valuation K`.
- `Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF K L : CompleteDVF.{0,0} L`
  (adapted M248.006, module `…FiniteExtensionCompleteDVF.Chosen`) is the
  complete discrete valuation on `L` chosen by `Classical.choose` from the
  published existence theorem
  `exists_integralClosure_standard_completeDVF_extension.{0,0,0} K L (localCompleteDVF K)`.

`CompleteDVF.valuation` is the valuation stored in the bundle, and
`Valuation.valuationSubring` is Mathlib's valuation subring of a valuation on
a field.

In words: let `K` be a nonarchimedean local field and `L` a finite separable
extension of `K`, both in `Type 0`. Then the chosen valuation on `L` extends
the canonical valuation of `K`. With such an extension witness, the
valuation ring of the chosen valuation is the integral closure in `L` of
the canonical valuation ring of `K`, and it is a finite module over that
ring.

### Scope and absence of premises

Both carriers are in `Type 0`, as in the source and as required by the
chosen definition, whose value is a `CompleteDVF.{0,0} L`. `K` is a
nonarchimedean local field in Mathlib's sense (`IsNonarchimedeanLocalField K`)
for arbitrary supplied valuative relation and topology. `L` is an arbitrary
field. The algebra `K → L` is arbitrary supplied data, finite-dimensional
and separable.

No structure is placed on `L` beyond its field structure and this algebra:
no valuation, valuative relation, topology, uniformity or local-field
structure. The proposition has no premise beyond the telescope. In
particular it assumes no `HasExtension`, integral-closure, finite-module or
other conclusion certificate; these are exactly the conclusions. It declares
no instance.

The identity extension is included: for `L = K` with `Algebra.id`, Mathlib
supplies `FiniteDimensional K K` and `Algebra.IsSeparable K K`, so the
proposition specializes to `K` and `K`. A private check (below) specialized
it at `K K`.

## Local witness and scalar conventions

### Meaning of `Valuation.HasExtension`

`Valuation.HasExtension vR vA` is Mathlib's `Prop`-valued class
(`Mathlib/RingTheory/Valuation/Extension.lean`, lines 65–67). Its single
field states `vR.IsEquiv (vA.comap (algebraMap R A))`. Here it says that
the canonical valuation of `K` is equivalent (not necessarily equal) to the
restriction of the chosen valuation along the supplied `algebraMap K L`.
The prefix form `_root_.Valuation.HasExtension` denotes the same Mathlib
constant as the source's dot notation
`(localCompleteDVF K).valuation.HasExtension …`. The `_root_` prefix prevents
resolution inside the `Langlands.NYLL` namespaces.

### Scalar structures in the two conjuncts

`letI` binds the existential witness `hExt` as a local instance for the two
conjuncts only. Under it, the scalar structures are the following. A private
check (below) confirmed each of them by elaboration.

- **Integral-closure conjunct.** `IsIntegralClosure A R B` needs algebras
  `R → B` and `A → B`, but no algebra `R → A`. Here `B` is the supplied
  field `L`, `A` is the chosen valuation subring and `R` is the canonical
  valuation subring of `K`. The algebra from the chosen subring to `L` is its
  actual inclusion (Mathlib's `ValuationSubring` algebra instance). The
  algebra from the base subring to `L` is
  `Algebra.ofSubsemiring` of the supplied `Algebra K L`. That is, its map is
  the inclusion into `K` followed by the supplied `algebraMap K L`. Neither
  algebra mentions `hExt`. The conjunct elaborates with no `HasExtension`
  instance in scope, and it is the same proposition with or without the
  `letI` (checked by `Iff.rfl`). It is the actual `IsIntegralClosure`
  property for these two rings inside `L`: the inclusion of the chosen ring
  is injective, and an element of `L` is integral over the base ring exactly
  when it lies in the chosen ring. It is not an abstract ring equivalence
  and involves no independently chosen target.
- **Finiteness conjunct.** `Module.Finite` uses the module structure
  `Algebra.toModule` of Mathlib's
  `Valuation.HasExtension.instAlgebra_valuationSubring` (lines 182–183),
  instantiated with `hExt`. Its algebra map sends `a` to the element of the
  chosen subring whose image in `L` is `algebraMap K L (a : K)`
  (Mathlib's `coe_algebraMap_valuationSubring_eq`, lines 186–187). Hence
  `a • b` is the element of the chosen subring whose image in `L` is
  `algebraMap K L (a : K) * (b : L)`. Under the same witness, Mathlib also
  provides the towers `IsScalarTower K₀ K L` and `IsScalarTower K₀ L₀ L`
  (lines 189–193), where `K₀` and `L₀` are the two valuation subrings.

The witness enters only through this module structure. `HasExtension` is a
`Prop`, so any two witnesses are definitionally equal by proof irrelevance.
The resulting `Module.Finite` propositions coincide (checked by `Iff.rfl`).

## Why the M248.008 instance becomes a local `letI`

In the source, M248.007 proves the `HasExtension` fact, and M248.008 declares
it as a global instance, `chosenLocalExtensionCompleteDVF.instHasExtension`.
M248.009 does not need that instance, but M248.010 does: its
`Module.Finite` statement needs a module structure of the base valuation
subring on the chosen one. The global M248.008 instance supplies it through
`instAlgebra_valuationSubring`.

This unit cannot keep that arrangement:

- It publishes statements only. A global instance needs a value, here a proof
  of M248.007, which this unit does not contain.
- Its contract forbids introducing a global instance.

The proposition therefore states the M248.007 conclusion as an existential,
`∃ hExt`, and installs that witness with `letI` for the other two
conclusions. This preserves the source meaning. Any proof of M248.007 is a
witness for the existential. Conversely, the witness obtained from the
existential gives exactly the module structure that the M248.008 instance
would give, by proof irrelevance (previous section). So the M248.010
conjunct is the source's M248.010 statement. The M248.009 conjunct does not
depend on the witness at all.

A private check derived the three source conclusions from this proposition,
written in the source's spelling. M248.009 and M248.010 were derived with
the M248.007 witness installed locally, in place of the global instance.

## Original-to-adapted declaration map

| Source unit | Source declaration (lines) | Adapted counterpart |
| --- | --- | --- |
| M248.001 | `localCompleteDVF` (34–55) | `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`, published separately; the base |
| M248.003, M248.004 | `localCompleteDVF_integerRing_isIntegralClosure`, `localCompleteDVF_integerRing_moduleFinite` | not adapted here; canonical integer-ring comparisons remain separate |
| M248.005 | private `chosenLocalExtensionCompleteDVF_exists` (114–128) | no declaration; the published chosen definition applies the published existence theorem directly |
| M248.006 | `chosenLocalExtensionCompleteDVF` (130–138) | `Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF`, published separately, used unchanged |
| M248.007 | `chosenLocalExtensionCompleteDVF_hasExtension` (140–150) | the existential of `ChosenLocalExtensionPropertiesStatement` (this module) |
| M248.008 | `chosenLocalExtensionCompleteDVF.instHasExtension` (152–161) | omitted; replaced by the local `letI` binding |
| M248.009 | `chosenLocalExtensionCompleteDVF_isIntegralClosure` (163–174) | the first conjunct (this module) |
| M248.010 | `chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite` (176–192) | the second conjunct (this module) |
| M248.011 | `chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension` (194–204) | not adapted here; remains separate |

## Differences from the source

- **Grouping.** Three separate theorem signatures become one closed
  proposition. The shared telescope, which each source theorem takes as
  declaration arguments, is quantified inside the proposition. The three
  conclusions are joined by the existential and a conjunction. The
  proofs are omitted.
- **Instance.** The global M248.008 instance is replaced by the local
  `letI` binding, as explained above.
- **Spelling.** The source writes the valuation subrings with the
  `CompleteDVF.valuationSubring` abbreviation. Here they are written
  `….valuation.valuationSubring`, which is what that abbreviation unfolds
  to. `HasExtension` is written in prefix form. A private check proved by
  `Iff.rfl` that the proposition equals its source spelling, with dot
  notation and the abbreviation.
- **Namespace and name.** The namespace is prefixed with `Langlands.NYLL`.
  The new name `ChosenLocalExtensionPropertiesStatement` replaces the three
  theorem names, since it names a proposition rather than a proof.
- **Imports.** The source imports `NonarchimedeanLocalField.Basic`,
  `Mathlib.Algebra.Order.Hom.Units`, `Mathlib.NumberTheory.LocalField.Basic`,
  the NYLL `FiniteIntegralClosure` module and `ValuedAdicComplete`. They are
  replaced by:
  - the published module
    `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Chosen`,
    which supplies `chosenLocalExtensionCompleteDVF` and, through its own
    imports, `localCompleteDVF`, `CompleteDVF`, `IsNonarchimedeanLocalField`,
    `FiniteDimensional` and `Algebra.IsSeparable`;
  - `Mathlib.RingTheory.Valuation.Extension` (`Valuation.HasExtension` and
    `instAlgebra_valuationSubring`);
  - `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs`
    (`IsIntegralClosure`);
  - `Mathlib.RingTheory.Finiteness.Defs` (`Module.Finite`).

  No external NYLL repository module is imported.
- **Unused context.** The source opens `scoped ValuativeRel` and declares
  universes `u v y`. Neither is used here, since everything is in `Type 0`,
  and both are omitted.

## Statement-versus-proof boundary

This unit publishes the proposition and this explanation only. It proves
none of M248.007, M248.009 or M248.010, and it declares no instance. A proof
of `ChosenLocalExtensionPropertiesStatement` is a separate later unit.

The following are outside this proposition and remain separate:

- M248.011, uniqueness of the valuation extension of the canonical base to
  the chosen target;
- comparison of the chosen valuation with an independently supplied
  valuation on `L`, or of the chosen target with another target;
- the canonical integer-ring comparisons M248.003 and M248.004;
- the fundamental identity of M245.018 for the chosen target;
- the host inertia and finite `Type 0` reciprocity results.

The published chosen definition is used unchanged.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a definition with no level parameters, and
`statement_returns_prop: true`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A separate private check module, not submitted, did the following:

- It printed the definition with universes and with explicit instances. The
  integral-closure conjunct uses `Algebra.ofSubsemiring` of the supplied
  `Algebra K L` and the `ValuationSubring` inclusion algebra, without `hExt`.
  The finiteness conjunct uses `Algebra.toModule` of
  `instAlgebra_valuationSubring` at `hExt`.
- It checked by `Iff.rfl` that the proposition equals its source spelling.
- It checked that the integral-closure conjunct elaborates without a
  `HasExtension` instance and agrees with its `letI` form.
- Under a witness, it checked the algebra-map, inclusion and scalar
  multiplication formulas and the module instance above by `rfl`, and the
  two scalar towers by instance search.
- It checked by `Iff.rfl` that two witnesses give the same `Module.Finite`
  proposition.
- It derived the three source conclusions from the proposition.
- It specialized the proposition to the identity extension `K K`.
- As a feasibility check only, it proved the proposition from the published
  existence theorem by `Classical.choose_spec` and Mathlib's
  `IsIntegralClosure.finite`, using only the standard axioms. That proof is
  not part of this unit.

These checks establish compilation and the correspondence stated here.
Semantic review and publication are separate steps.

## Attribution and modifications

The complete 206-line original was read. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The source-specific context is the namespace at line 24, universes at line
30, M248.005–M248.006 at lines 114–138, and M248.007–M248.011 at lines
140–204.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source partition `notes/reuse/nyll-public-port/m241-m258.md` (rows for
M248.007–M248.011) records no patch10 compatibility edit for M248. No
applicable source erratum was found in the checked project and Library notes
on 31 October 2026.

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

On 31 October 2026, Worker 785 extracted the three statements, grouped them,
made the instance, spelling, namespace and import changes listed above, and
wrote this explanation. Worker 106 supplied routing only. The published
inputs `localCompleteDVF` and `chosenLocalExtensionCompleteDVF` (both adapted
by Worker 785) are imported by Lean name. No unpublished implementation or
draft from another worker was reused.
