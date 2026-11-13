# Relative norm of the maximal ideal of a local-field extension: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrankStatement K L`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.016 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).
It uses the published proofs of M162.012 and M162.015 and no source helper.

## Target and binders

The theorem's complete telescope and conclusion are

```lean
open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

theorem relNorm_maximalIdeal_eq_pow_residue_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    relNorm_maximalIdeal_eq_pow_residue_finrankStatement K L
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. The published statement
unfolds to

```lean
Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
  (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L]
```

where `𝓂[K]` is `IsLocalRing.maximalIdeal 𝒪[K]` and `𝓀[K]` is
`IsLocalRing.ResidueField 𝒪[K]`. The proof module registers the same local
instance attribute on `FractionRing.liftAlgebra` as the statement modules; it
is needed here because the M162.012 and M162.015 statements are elaborated
with it.

The direct imports are the published modules

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U016.Statements`,
  for the target;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U012.Proofs`,
  for `relNorm_eq_pow_inertiaDeg_of_isSeparable` (M162.012);
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U015.Proofs`,
  for `fractionRing_integerRing_isSeparable` (M162.015).

Together with their Mathlib imports they supply the whole API used below.

## Implemented proof

The proof is the source proof with one added rewrite step.

1. **Separability of the fraction fields.** A `let` binding introduces the
   instance `Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L])`
   with value `fractionRing_integerRing_isSeparable K L` (M162.015). That
   theorem's type is the statement constant
   `fractionRing_integerRing_isSeparableStatement K L`, which unfolds by
   definition to the ascribed type, so the binding elaborates unchanged.
2. **The M162.012 equation.** `h` is
   `relNorm_eq_pow_inertiaDeg_of_isSeparable 𝒪[K] 𝒪[L] 𝓂[L] 𝓂[K]`, of type
   `relNorm_eq_pow_inertiaDeg_of_isSeparableStatement 𝒪[K] 𝒪[L] 𝓂[L] 𝓂[K]`.
   Instance synthesis supplies its hypotheses from Mathlib, as Worker 85
   recorded for the target and as a development probe with `#synth`
   confirmed:
   - `IsDedekindDomain 𝒪[K]` and `IsDedekindDomain 𝒪[L]` come from
     `IsPrincipalIdealRing.isDedekindDomain`
     (`Mathlib/RingTheory/DedekindDomain/Basic.lean`, line 170), since
     `𝒪[K]` is a discrete valuation ring by Mathlib's local-field instance
     (`Mathlib/NumberTheory/LocalField/Basic.lean`, line 108);
   - `Module.IsTorsionFree 𝒪[K] 𝒪[L]` is
     `Valuation.HasExtension.instIsTorsionFreeInteger`
     (`Mathlib/RingTheory/Valuation/Extension.lean`, line 146);
   - `(𝓂[L]).LiesOver 𝓂[K]` is the residue-field instance
     `IsLocalRing.ResidueField.instLiesOverMaximalIdeal`
     (`Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`, line 184), using
     that `𝒪[K] → 𝒪[L]` is a local homomorphism
     (`Valuation.HasExtension.instIsLocalHomValuationInteger`,
     `Extension.lean`, line 154);
   - maximality of `𝓂[K]` and `𝓂[L]` is `IsLocalRing.maximalIdeal.isMaximal`;
   - `Module.Finite 𝒪[K] 𝒪[L]` is the theorem's hypothesis, and the
     separability hypothesis is the `let` binding of step 1.
3. **Unfolding and the inertia degree.** `rw … at h` first rewrites with
   `relNorm_eq_pow_inertiaDeg_of_isSeparableStatement`, which unfolds the
   statement constant to
   `Ideal.relNorm 𝒪[K] 𝓂[L] = 𝓂[K] ^ (𝓂[L]).inertiaDeg 𝒪[K]`. It then
   rewrites with `Ideal.inertiaDeg_eq_of_isMaximal 𝓂[K] 𝓂[L]`
   (`Mathlib/RingTheory/RamificationInertia/Inertia.lean`, line 111), which
   for maximal ideals `q` lying over `p` gives
   `q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q)`. Now `h` says
   `Ideal.relNorm 𝒪[K] 𝓂[L] = 𝓂[K] ^ Module.finrank (𝒪[K] ⧸ 𝓂[K]) (𝒪[L] ⧸ 𝓂[L])`.
4. **Final step.** `exact h` closes the goal. The statement constant of the
   goal unfolds by definition, and `Module.finrank (𝒪[K] ⧸ 𝓂[K]) (𝒪[L] ⧸ 𝓂[L])`
   agrees with `Module.finrank 𝓀[K] 𝓀[L]` by definitional unfolding:
   `IsLocalRing.ResidueField R` is defined as `R ⧸ maximalIdeal R`
   (`Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean`, line 30). A
   development probe checked this equality of the two `finrank` expressions
   by `rfl` in the approved environment.

No auxiliary declaration or global instance is introduced. The `let` binding
is local to the proof, and the local instance attribute on
`FractionRing.liftAlgebra` is scoped to this module.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the file-level local instance attribute at line 321
and the theorem at lines 389–410 (docstring 389–391, statement 392–403,
proof 403–410). The theorem lies outside every `section`, and no `variable`
is in scope at that point. The complete pinned file was read.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank` (M162.016) | `Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank`, proving the published target |
| Same theorem's statement | Existing `relNorm_maximalIdeal_eq_pow_residue_finrankStatement` |
| `LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable` (M162.012), used | Published `Langlands.NYLL.LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable`, imported |
| `LocalClassFieldTheory.fractionRing_integerRing_isSeparable` (M162.015), used | Published `Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparable`, imported |

Modifications by Worker 173 on 13 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the U016 Statements module and the published U012 and U015
  proof modules;
- the theorem's type is the statement constant
  `relNorm_maximalIdeal_eq_pow_residue_finrankStatement K L` instead of the
  equation it unfolds to;
- the `rw … at h` list starts with
  `relNorm_eq_pow_inertiaDeg_of_isSeparableStatement`. In the source, `h`
  has the unfolded equation as its type; here the imported M162.012 theorem
  has the statement constant as its type, and `rw` does not see through it.
  A development check confirmed that the unchanged source step fails with
  “Did not find an occurrence of the pattern” at exactly this point;
- every other declaration of the source file is omitted.

The theorem name, docstring, binders, the local instance attribute and the
remaining proof steps are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`. Searches of the workspace, the
current Library, staging and shared drafts found no earlier proof of this
target.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development
check built the module with no errors and no warnings and found a theorem with
level parameters `u`, `v` using only the axioms `propext`, `Classical.choice`
and `Quot.sound`. This check is not independent semantic acceptance or
Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI
Codex)”, released under Apache-2.0. The Lean file carries Worker 173's dated
modification record. Worker 173 adapted this proof directly from the pinned
original and wrote this companion. Worker 85's statement is used unchanged;
the imported statement and proof modules and their paired Markdown remain
frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are byte-identical to the
retained originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This module proves only M162.016. The norm-valuation results M162.017–M162.019
that consume it are outside this task.
