# Actual unique-extension Herbrand laws: proofs

This module proves the unchanged closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.UniqueExtensionHerbrandLawsStatement`
from the published [target](LawsStatement.md). Its aggregate theorem, in
namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`,
has the complete type

```lean
theorem uniqueExtensionHerbrandLaws :
    UniqueExtensionHerbrandLawsStatement.{u, v, w, x}
```

The four universe levels `u v w x` are arbitrary and independent: `u` and
`w` are the universes of the fields `K` and `L`, and `v` and `x` those of
the value groups of the supplied DVFs `base : DVF.{u,v} K` and
`target : DVF.{w,x} L`; the comparison valuation in `huniq` has universe
`x`, as in the target. No two levels are identified. The theorem has no
outer term parameters, instances or hypotheses.

The aggregate introduces the target's implicit fields `K` and `L`, the
supplied `Field K`, `Field L` and `Algebra K L` instances, the implicit
supplied DVFs `base` and `target`, the supplied
`base.valuation.HasExtension target.valuation` instance and the explicit
`huniq : HasUniqueValuationExtension.{u,v,w,x,x} base target`. It then
constructs the target's right-associated conjunction
`evaluation1 ∧ evaluation2 ∧ (∀ [FiniteDimensional K L], sixLaws)`.
Every helper and every conjunct uses this same `base`, `target` and
`huniq`. The group throughout is Mathlib's `Gal(L/K)`, the actual algebra
automorphism group `L ≃ₐ[K] L`.

The module imports only the published target and the published
[generic inverse proof](../../Herbrand/Function/InverseProof.md). The
target imports the published [actual definitions](Definitions.md) and
[actual lower filtration](LowerFiltration.md); the generic inverse proof
imports the published [generic analytic proof](../../Herbrand/Function/AnalyticProof.md).
All published pairs, including the target pair, remain unchanged.

## Helpers and scope blocks

The eight helpers lie in the namespace above. Each takes the same supplied
data as the target, in the order implicit `{K : Type u} {L : Type w}`,
`[Field K] [Field L] [Algebra K L]`, implicit `{base}` and `{target}`,
`[base.valuation.HasExtension target.valuation]`, and then explicit
`huniq`. In the table, `φ` abbreviates
`herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq`,
`ψ` abbreviates
`inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq`,
`F` abbreviates
`lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq`,
and `G_s` and `G^t` abbreviate
`lowerRamificationGroup (base := base) (target := target) huniq s` and
`upperRamificationGroupOfUniqueExtension (base := base) (target := target) huniq t`.
The generic functions are
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction`
and `….inverseHerbrandFunction`.

| Helper | Scope | Further binder | Conclusion | Attribute |
| --- | --- | --- | --- | --- |
| `herbrandFunctionOfUniqueExtension_apply` | unrestricted | `(s : ℝ)` | `φ s = herbrandFunction F s` | `@[simp]` |
| `inverseHerbrandFunctionOfUniqueExtension_apply` | unrestricted | `(t : ℝ)` | `ψ t = inverseHerbrandFunction F t` | `@[simp]` |
| `herbrandFunctionOfUniqueExtension_psi` | `[FiniteDimensional K L]` | `(t : ℝ)` | `φ (ψ t) = t` | `@[simp]` |
| `inverseHerbrandFunctionOfUniqueExtension_eta` | `[FiniteDimensional K L]` | `(s : ℝ)` | `ψ (φ s) = s` | `@[simp]` |
| `herbrandFunctionOfUniqueExtension_strictMono` | `[FiniteDimensional K L]` | none | `StrictMono φ` | none |
| `inverseHerbrandFunctionOfUniqueExtension_strictMono` | `[FiniteDimensional K L]` | none | `StrictMono ψ` | none |
| `upperRamificationGroupOfUniqueExtension_herbrandFunction` | `[FiniteDimensional K L]` | `(s : ℝ)` | `G^(φ s) = G_s` | `@[simp]` |
| `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff` | `[FiniteDimensional K L]` | `{t : ℝ}` | `-1 ≤ ψ t ↔ -1 ≤ t` | none |

The two evaluations precede the module's `FiniteDimensional` section, so
their signatures have no finite-dimensionality hypothesis. The six later
helpers lie in that section, where the instance
`[FiniteDimensional K L]` follows the `HasExtension` instance and precedes
`huniq`. The real arguments are explicit except the implicit `{t : ℝ}` of
the final equivalence, as in the source. The five `@[simp]` attributes are
exactly the source ones.

## Finiteness of the actual automorphism group

The generic laws of the published analytic and inverse proofs are stated
for a group `G` with a `Finite G` instance. In the finite-dimensional
section, Lean's instance search supplies `Finite Gal(L/K)` from existing
Mathlib instances: `Finite.algEquiv` (`Mathlib/Algebra/Algebra/Equiv.lean`)
reduces it to finiteness of `L →ₐ[K] L`, which the anonymous instance
`instFiniteAlgHomOfFinite`
(`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`) derives from
`Module.Finite K L`, that is from `[FiniteDimensional K L]`. This module
declares no instance, global or local, and adds no finite-group premise.

## Proofs

The two evaluations hold by `rfl`: the published definitions of `φ` and
`ψ` are exactly the generic `herbrandFunction` and `inverseHerbrandFunction`
applied to `F`.

The two composition identities are the generic
`herbrandFunction_inverseHerbrandFunction` and
`inverseHerbrandFunction_herbrandFunction` (from the inverse proof)
applied to `F` and the real argument. Strict monotonicity of `φ` is the
generic `herbrandFunction_strictMono` (from the analytic proof, reached
through the inverse proof's import) applied to `F`, and strict monotonicity
of `ψ` is the generic `inverseHerbrandFunction_strictMono` applied to `F`.
Each of these terms elaborates against the actual helper types because
`φ` and `ψ` unfold definitionally to the generic functions on `F`.

The upper-group evaluation is `congrArg` of the actual real lower-group
family `fun r => lowerRamificationGroup (base := base) (target := target) huniq r`
applied to the equation `ψ (φ s) = s` of
`inverseHerbrandFunctionOfUniqueExtension_eta`. Its left side is
`G_(ψ (φ s))`, which is definitionally `G^(φ s)` by the published
definition of the upper group, and its right side is `G_s`.

The final equivalence is the generic
`inverseHerbrandFunction_mem_Ici_neg_one_iff` applied to `F`, made
available by a declaration-local `open … in`. Its statement
`ψ t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1)` is definitionally
`-1 ≤ ψ t ↔ -1 ≤ t`, and the implicit `t` is inferred.

## Aggregate

The aggregate introduces all binders of the target and supplies the two
unrestricted evaluation helpers, each partially applied to `huniq` so that
the clause-local real variable remains universally quantified. It then
introduces the target's internal `FiniteDimensional K L` instance and
supplies the six later helpers, applied to `huniq`, in the target's
order. The last conjunct quantifies `t` explicitly, so it is supplied as
`fun _ => inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff huniq`,
with the implicit argument of the helper inferred. Completeness, residue
separability, `IsGalois`, eventual triviality, cutoff conditions, inverse
identities and monotonicity are not premises. The theorem depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source and adaptations

The source is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`, lines 88–191](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean#L88-L191),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The whole file was read;
its SHA-256 is
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`. Its
ambient data are at lines 32–35 and its finite-dimensional section,
including the local `generalDVFGalFintype` instance, at lines 65–68. The
registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public
[M305 partition](../../../../../../notes/reuse/nyll-public-port/m289-m312.md#m305)
records no patch10 change.

| Source unit | Lines | Adapted helper | Aggregate position |
| --- | --- | --- | --- |
| M305.006 `herbrandFunctionOfUniqueExtension_apply` | 88–98 | Same name, signature and proof `rfl` | Clause 1, unrestricted |
| M305.007 `inverseHerbrandFunctionOfUniqueExtension_apply` | 100–110 | Same name, signature and proof `rfl` | Clause 2, unrestricted |
| M305.008 `herbrandFunctionOfUniqueExtension_psi` | 112–122 | Same name, signature and proof | Clause 3, finite-dimensional block |
| M305.009 `inverseHerbrandFunctionOfUniqueExtension_eta` | 124–134 | Same name, signature and proof | Clause 4, finite-dimensional block |
| M305.010 `herbrandFunctionOfUniqueExtension_strictMono` | 136–144 | Same name, signature and proof | Clause 5, finite-dimensional block |
| M305.011 `inverseHerbrandFunctionOfUniqueExtension_strictMono` | 146–154 | Same name, signature and proof | Clause 6, finite-dimensional block |
| M305.013 `upperRamificationGroupOfUniqueExtension_herbrandFunction` | 166–178 | Same name, signature and proof | Clause 7, finite-dimensional block |
| M305.014 `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff` | 180–191 | Same name, signature and proof | Clause 8, finite-dimensional block, by abstraction over `t` |

The source data M305.004/.005/.012 (the two wrappers and the upper group)
and the lower filtration are imported from their published modules, not
redeclared. The proofs are the source proofs. The textual changes are:
the namespace gains `Langlands.NYLL`, and the DVF, unique-extension and
generic Herbrand names are written fully qualified under that prefix
instead of relative to the source's namespace and
`open ValuationTheory.DiscreteValuationField`, with the `huniq` binder
re-wrapped so that its type starts on its own line; the source's `omit [FiniteDimensional K L] in`
before the two evaluations is replaced by placing them before the
finite-dimensional section; the final helper's
`open _root_.RamificationTheory.… in` becomes the corresponding
`Langlands.NYLL` path; and the `noncomputable section` and the local
`generalDVFGalFintype : Fintype Gal(L/K)` instance are omitted, since the
generic laws need only the `Finite Gal(L/K)` instance described above.
The original imports are replaced by the published target and generic
inverse proof.

Worker 1237 implemented these adaptations, the exact closed aggregate and
this companion. Worker 106 supplied the original-source and interface
analysis, the exact-target and helper design and the proof-route
analysis.

The original copyright and authorship header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is Apache-2.0; the Lean header records the modifications. The
existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively; the root NOTICE inventory has no entry for this source
file. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, rather than upstream
Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
