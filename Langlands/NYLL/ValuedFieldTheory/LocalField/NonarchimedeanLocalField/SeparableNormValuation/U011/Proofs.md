# Normal closures of separable fraction-field extensions are Galois: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparableStatement R S`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.011 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).
Following the task, the private source helpers M162.002–M162.006 that this
proof needs are proved inside this module as `private` theorems; they are not
separate targets.

## Target and binders

The theorem's complete telescope and conclusion are

```lean
attribute [local instance] FractionRing.liftAlgebra

theorem ringNormalClosure_isGalois_of_isSeparable
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    ringNormalClosure_isGalois_of_isSeparableStatement R S
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. `R`, `S` and the seven
instance binders up to `[Module.IsTorsionFree R S]` come from the section's
`variable` line, as in the source. The proof module registers the same local
instance attribute `FractionRing.liftAlgebra` as the statement module, so the
separability hypothesis is elaborated with the same algebra structure
`FractionRing.liftAlgebra R (FractionRing S)` as the statement's binder.

The published statement unfolds to

```lean
IsGalois (FractionRing R) (FractionRing (Ring.NormalClosure R S))
```

where the algebra structure `Frac R → Frac (Ring.NormalClosure R S)` is again
`FractionRing.liftAlgebra`. The theorem assumes only that `R → S` is a finite,
torsion-free extension of integral domains and that `Frac S / Frac R` is
separable. It assumes neither integral closedness, nor Dedekind, nor that
`Frac R` is perfect.

The sole direct import is the published module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U011.Statements`.
Through its imports `Mathlib.FieldTheory.SeparableClosure` and
`Mathlib.RingTheory.Ideal.Norm.RelNorm` it supplies the whole Mathlib API used
below.

## Implemented proof

Write `K = Frac R`, `L = Frac S`, `A = AlgebraicClosure L`,
`E = IntermediateField.normalClosure K L A` and `T = Ring.NormalClosure R S`.
By definition (`Mathlib/RingTheory/NormalClosure.lean`, line 63), `T` is
`integralClosure S E`. The proof is the source proof, kept unchanged, and
consists of five private helpers and the final step.

1. **M162.002 `intermediateNormalClosure_isSeparable_of_isSeparable`.** For
   fields `K`, `L`, `A` with a scalar tower `K → L → A` and `L / K`
   separable, `E` is separable over `K`. The proof unfolds `E` by `change` to
   the supremum `⨆ f : L →ₐ[K] A, f.fieldRange`. Each `f.fieldRange` is
   `K`-isomorphic to `L` through `AlgEquiv.ofInjectiveField f`
   (`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`, line 639), hence
   separable by `AlgEquiv.Algebra.isSeparable`
   (`Mathlib/FieldTheory/Separable.lean`, line 608), and a supremum of
   separable intermediate fields is separable by
   `IntermediateField.isSeparable_iSup`
   (`Mathlib/FieldTheory/SeparableClosure.lean`, line 231).
2. **M162.003 `intermediateNormalClosure_isGalois_of_isSeparable`.** If in
   addition `L / K` is finite and `A / K` is normal, then `E / K` is Galois.
   The `IsGalois` structure is built from step 1 and from Mathlib's
   `normalClosure.normal` (`Mathlib/FieldTheory/Normal/Closure.lean`,
   line 167).
3. **M162.004 `intermediateNormalClosure_finiteDimensional_top`.** If `L / K`
   is finite, then `E` is finite-dimensional over `L` for the algebra
   structure `normalClosure.algebra K L A` (same file, line 181). This is
   `Module.Finite.right K L E` (`Mathlib/FieldTheory/Tower.lean`, line 55),
   whose hypothesis that `E / K` is finite is Mathlib's instance
   `normalClosure.is_finiteDimensional`
   (`Mathlib/FieldTheory/Normal/Closure.lean`, line 173).
4. **M162.005 `ringNormalClosure_isFractionRing`.** With `Algebra S E` the
   composite `S → L → E`, the scalar tower `S → L → E` (proved by `rfl` on
   `algebraMap`) and `Algebra T E` the subalgebra inclusion of
   `integralClosure S E`, `E` is a fraction field of `T`. After `change` to
   `IsFractionRing (integralClosure S E) E`, this is
   `integralClosure.isFractionRing_of_finite_extension L E`
   (`Mathlib/RingTheory/Localization/Integral.lean`, line 398), using step 3.
   Here `FiniteDimensional K L` is Mathlib's instance
   `instFiniteDimensionalFractionRingOfFinite`
   (`Mathlib/RingTheory/Algebraic/Integral.lean`, lines 695–700), derived
   from `[Module.Finite R S]` and torsion-freeness.
5. **M162.006 `ringNormalClosure_isGalois_transport`.** If `E / K` is
   Galois, then `Frac T / K` is Galois. The helper sets up the scalar towers
   `S → T → E` (`IsScalarTower.subalgebra'`), `R → L → E`, `R → S → E` and
   `R → T → E` (`IsScalarTower.to₁₃₄`, `IsScalarTower.to₁₂₄`) and the
   fraction-field structure of step 4. It then applies
   `IsGalois.of_equiv_equiv` (`Mathlib/FieldTheory/Galois/Basic.lean`,
   line 182) to ring isomorphisms `f : K ≃+* FractionRing R` and
   `g : E ≃+* FractionRing T`, the inverses of `FractionRing.algEquiv R K` and
   `FractionRing.algEquiv T E`
   (`Mathlib/RingTheory/Localization/FractionRing.lean`, line 793). Here `K`
   is `FractionRing R` itself, so `f` is the canonical identification; the
   target algebra structure on the codomains is `FractionRing.liftAlgebra`. The
   required commuting square is checked pointwise by `ext` and
   `simpa using IsFractionRing.algEquiv_commutes …` (same file, line 308).
6. **Final step.** The theorem applies step 5 to step 3's Galois property of
   `E / K`. Instance synthesis supplies the remaining arguments of step 3:
   `FiniteDimensional K L` from `instFiniteDimensionalFractionRingOfFinite`,
   normality of `A / K` from `IsAlgClosure.normal`
   (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, line 275) and the tower
   `K → L → A` from `AlgebraicClosure.instIsScalarTower`; a development probe
   with `#synth` identified these instances. The separability of `L / K` is
   the theorem's hypothesis.

All auxiliary structures are `let`/`letI` bindings inside the helper proofs or
statements. No global instance is added. The local instance attribute on
`FractionRing.liftAlgebra` is scoped to this module. The proof never uses
Mathlib's instance `IsGalois K (FractionRing T)` (`NormalClosure.lean`,
line 119), which needs `PerfectField K`.

## Private helpers

| Source unit and line | Source declaration (private) | Declaration in this module |
| --- | --- | --- |
| M162.002, line 50 | `intermediateNormalClosure_isSeparable_of_isSeparable` | `private theorem` of the same name |
| M162.003, line 62 | `intermediateNormalClosure_isGalois_of_isSeparable` | `private theorem` of the same name |
| M162.004, line 76 | `intermediateNormalClosure_finiteDimensional_top` | `private theorem` of the same name |
| M162.005, line 89 | `ringNormalClosure_isFractionRing` | `private theorem` of the same name |
| M162.006, line 123 | `ringNormalClosure_isGalois_transport` | `private theorem` of the same name |
| M162.001, line 43 and M162.010, line 246 | anonymous local instances `FractionRing.liftAlgebra R (FractionRing S)` | `attribute [local instance] FractionRing.liftAlgebra` |

The helpers keep their source names, docstrings, binders, statements and
proofs. Being `private`, they are invisible outside this module, and they are
not separate Library targets. The partition reserves
`Langlands.NYLL.PortInternal.M162.d002`–`d006` for them; those public names are
not used. M162.002 is used by M162.003, M162.004 by M162.005, M162.005 by
M162.006, and M162.003 and M162.006 by the final step. M162.007–M162.009 are
not needed for this theorem and are omitted.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the section `SeparableIdealNorm` (lines 36–44 for its
telescope and local instance M162.001) with the helpers at lines 46–161,
and the section `SeparableIdealNormGalois` (lines 240–265) with its local
instance M162.010 at lines 246–247 and the theorem at lines 249–263. The
complete pinned file was read.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable` (M162.011) | `Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable`, proving the published target |
| Same theorem's statement | Existing `ringNormalClosure_isGalois_of_isSeparableStatement` |
| Private helpers M162.002–M162.006 | Private theorems of this module (table above) |

Modifications by Worker 173 on 13 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the sole U011 Statements import;
- the theorem's type is the statement constant
  `ringNormalClosure_isGalois_of_isSeparableStatement R S` instead of the
  `IsGalois` proposition it unfolds to;
- the anonymous local instances M162.001 and M162.010 are replaced by the
  local instance attribute on `FractionRing.liftAlgebra`, as in the statement
  module. Each source use of these instances is the term
  `FractionRing.liftAlgebra R (FractionRing S)` or, with `T` in place of `S`,
  `FractionRing.liftAlgebra R (FractionRing T)`, which is what instance
  synthesis now produces;
- the section variables `[IsIntegrallyClosed R] [IsIntegrallyClosed S]` and
  the two `omit … in` commands are dropped. The source omits these variables
  for M162.005 and M162.006, and M162.002–M162.004 do not mention `R` or `S`,
  so no used declaration takes them;
- the generic helpers M162.002–M162.004 are made `private` exactly as in the
  source, and M162.007–M162.009 and every declaration after line 265 are
  omitted.

The theorem name and docstring, all helper statements and every proof step are
kept. The upstream proof needed no change in the approved environment.

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
the imported statement module and its paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are byte-identical to the
retained originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This module proves only M162.011. The finiteness and Dedekind properties of
`Ring.NormalClosure R S` (M162.007, M162.009) and the relative-norm formula
M162.012 belong to the separate U012 proof.
