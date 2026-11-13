# Relative norm of a maximal ideal in a separable extension: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparableStatement R S P p`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.012 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).
Following the task, the private source helpers M162.002, M162.004, M162.007
and M162.009 that this proof needs are proved inside this module as `private`
theorems; they are not separate targets.

## Target and binders

The theorem's complete telescope and conclusion are

```lean
attribute [local instance] FractionRing.liftAlgebra

theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    (R : Type u) (S : Type v)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    relNorm_eq_pow_inertiaDeg_of_isSeparableStatement R S P p
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. `R`, `S` and the seven
instance binders up to `[Module.IsTorsionFree R S]` come from the section's
`variable` line, as in the source. The proof module registers the same local
instance attribute `FractionRing.liftAlgebra` as the statement module, so the
separability hypothesis has the statement's algebra structure
`FractionRing.liftAlgebra R (FractionRing S)`.

The published statement unfolds to

```lean
Ideal.relNorm R P = p ^ P.inertiaDeg R
```

Here `Ideal.relNorm R P` is Mathlib's relative ideal norm of `P` down to `R`,
and `P.inertiaDeg R` is the inertia degree of `P` over its contraction to `R`,
which is `p` by `[P.LiesOver p]`. The theorem assumes that `R → S` is a finite,
torsion-free extension of Dedekind domains with `Frac S / Frac R` separable,
and that `P` and `p` are maximal with `P` lying over `p`. It does not assume
that `Frac R` is perfect or that `Frac S / Frac R` is Galois.

The direct imports are the published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U012.Statements`
and the published M162.011 proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U011.Proofs`,
which supplies
`Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable`.
Both import only `Mathlib.FieldTheory.SeparableClosure` and
`Mathlib.RingTheory.Ideal.Norm.RelNorm` beyond the Library, and these supply
the Mathlib API used below.

## Implemented proof

Write `K = Frac R`, `L = Frac S`, `A = AlgebraicClosure L`,
`E = IntermediateField.normalClosure K L A` and `T = Ring.NormalClosure R S`,
which is by definition `integralClosure S E`
(`Mathlib/RingTheory/NormalClosure.lean`, line 63). The proof is the source
proof, kept unchanged. It mirrors Mathlib's perfect-base theorem
`Ideal.relNorm_eq_pow_of_isMaximal`
(`Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`, lines 437–447), with the three
facts about `T` that Mathlib derives from `PerfectField K` replaced by the
helpers below and by M162.011.

### Helpers

1. **M162.002 `intermediateNormalClosure_isSeparable_of_isSeparable`** and
   **M162.004 `intermediateNormalClosure_finiteDimensional_top`** are the
   same field-theoretic helpers as in the U011 proof module, with the same
   statements and proofs: if `L / K` is separable then `E / K` is separable
   (`change` to `⨆ f : L →ₐ[K] A, f.fieldRange`, then
   `IntermediateField.isSeparable_iSup` with
   `AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)`), and if
   `L / K` is finite then `E` is finite-dimensional over `L`
   (`Module.Finite.right K L E`). The U011 copies are `private` to that
   module and cannot be referenced here, so this module repeats them.
2. **M162.007 `ringNormalClosure_moduleFinite_of_isSeparable`.** Assume in
   addition that `S` is integrally closed and Noetherian and `L / K` is
   separable. Then `T` is a finite `S`-module. The proof sets up `Algebra S E`
   as the composite `S → L → E`, the scalar towers `S → L → E` (by `rfl`) and
   `S → T → E` (`IsScalarTower.subalgebra'`), the subalgebra inclusion
   `Algebra T E`, and `IsIntegralClosure T S E`
   (`integralClosure.isIntegralClosure`). From M162.004 it gets
   `FiniteDimensional L E`, from M162.002 `Algebra.IsSeparable K E`, and from
   `Algebra.isSeparable_tower_top_of_isSeparable`
   (`Mathlib/FieldTheory/Separable.lean`, line 632) `Algebra.IsSeparable L E`.
   After `change` to `Module.Finite S (integralClosure S E)` it concludes by
   `IsIntegralClosure.finite S L E (integralClosure S E)`
   (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`, line 175).
3. **M162.009 `ringNormalClosure_isDedekindDomain_of_isSeparable`.** If `S`
   is a Dedekind domain and `L / K` is separable, then `T` is a Dedekind
   domain. The set-up is the same as in M162.007, and after `change` to
   `IsDedekindDomain (integralClosure S E)` the proof concludes by
   `integralClosure.isDedekindDomain S L E` (same file, line 234).

### Main proof

1. `Module.Finite S T` is M162.007; its hypotheses `IsIntegrallyClosed S`,
   `IsNoetherianRing S` and `IsDomain R` come from the Dedekind instances.
   `Module.Finite R T` follows by `Module.Finite.trans S T`, and
   `IsDedekindDomain T` is M162.009.
2. The scalar tower `R → Frac S → Frac T` is `IsScalarTower.to₁₃₄` applied to
   `R → S → Frac S → Frac T`. The tower `Frac R → Frac S → Frac T` is
   `IsScalarTower.of_algebraMap_eq'`; the needed equality of ring maps
   `Frac R → Frac T` is checked by `IsFractionRing.ringHom_ext (A := R)` on
   elements of `R`, rewriting both sides with `IsScalarTower.algebraMap_apply`
   through the towers `R → Frac R → Frac T`, `R → Frac R → Frac S` and
   `R → Frac S → Frac T`.
3. `IsGalois K (Frac T)` is the imported M162.011 proof
   `ringNormalClosure_isGalois_of_isSeparable R S`; its type, the statement
   constant, unfolds definitionally to this `IsGalois` proposition and is
   accepted as such by the typed `let`. Then
   `IsGalois.tower_top_of_isGalois` (`Mathlib/FieldTheory/Galois/Basic.lean`,
   line 152) gives `IsGalois L (Frac T)`.
4. `Ideal.exists_maximal_ideal_liesOver_of_isIntegral`
   (`Mathlib/RingTheory/Ideal/GoingUp.lean`, line 370) gives a maximal ideal
   `Q` of `T` lying over `P`; `Ideal.LiesOver.trans`
   (`Mathlib/RingTheory/Ideal/Over.lean`, line 191) shows that `Q` lies over
   `p`.
5. Mathlib's Galois case `Ideal.relNorm_eq_pow_of_isPrime_isGalois`
   (`Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`, line 401) gives
   `h : relNorm R Q = p ^ Q.inertiaDeg R` for the Galois extension `T / R`.
   The proof rewrites `h` with `Ideal.relNorm_relNorm R S` (line 345) to
   `relNorm R (relNorm S Q)`; with the Galois case for `T / S` to
   `relNorm R (P ^ Q.inertiaDeg S)`; with `map_pow` to
   `relNorm R P ^ Q.inertiaDeg S`; with `Ideal.inertiaDeg_tower (R := R) P Q`
   (`Mathlib/RingTheory/RamificationInertia/Inertia.lean`, line 120) and
   `pow_mul` on the right to `(p ^ P.inertiaDeg R) ^ Q.inertiaDeg S`; and
   with `pow_left_inj` (`Mathlib/Algebra/Group/Torsion.lean`, line 41; its
   `IsMulTorsionFree (Ideal R)` argument is found by instance synthesis) to
   `relNorm R P = p ^ P.inertiaDeg R`. The `rwa`
   closes the goal with this hypothesis; the goal is the statement constant,
   which unfolds to it definitionally.
6. The side condition of `pow_left_inj`, `Q.inertiaDeg S ≠ 0`, follows from
   `Ideal.inertiaDeg_pos Q S` (same file, line 64) and
   `Nat.ne_zero_iff_zero_lt`.

All auxiliary structures are `let` bindings inside the proofs. No global
instance is added, and the local instance attribute on
`FractionRing.liftAlgebra` is scoped to this module.

## Private helpers

| Source unit and line | Source declaration (private) | Declaration in this module |
| --- | --- | --- |
| M162.002, line 50 | `intermediateNormalClosure_isSeparable_of_isSeparable` | `private theorem` of the same name |
| M162.004, line 76 | `intermediateNormalClosure_finiteDimensional_top` | `private theorem` of the same name |
| M162.007, line 166 | `ringNormalClosure_moduleFinite_of_isSeparable` | `private theorem` of the same name |
| M162.009, line 209 | `ringNormalClosure_isDedekindDomain_of_isSeparable` | `private theorem` of the same name |
| M162.001, line 43 and M162.008, line 204 | anonymous local instances `FractionRing.liftAlgebra R (FractionRing S)` | `attribute [local instance] FractionRing.liftAlgebra` |

The helpers keep their source names, docstrings, binders, statements and
proofs. Being `private`, they are invisible outside this module and are not
separate Library targets. The partition reserves
`Langlands.NYLL.PortInternal.M162.d002`, `d004`, `d007` and `d009` for them;
those public names are not used. M162.002 and M162.004 also occur, as
separate private theorems, in the U011 proof module. The other U011 helpers
M162.003, M162.005 and M162.006 enter only through the imported M162.011
theorem and are not repeated. M162.010 is the local instance of the M162.011
statement and is covered by the same attribute.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the section `SeparableIdealNorm` (telescope at lines
38–41, local instance M162.001 at 43–44, helpers M162.002 at 46–58, M162.004
at 74–84 and M162.007 at 163–194), the section `SeparableIdealNormDedekind`
(lines 198–238, local instance M162.008 at 204–205, M162.009 at 207–236) and
the section `SeparableIdealNormRelNorm` (lines 267–319, with the attribute at
line 274 and the theorem at 276–317). The complete pinned file was read.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable` (M162.012) | `Langlands.NYLL.LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable`, proving the published target |
| Same theorem's statement | Existing `relNorm_eq_pow_inertiaDeg_of_isSeparableStatement` |
| `LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable` (M162.011), used in the proof | Existing `Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable` (U011 proof module) |
| Private helpers M162.002, M162.004, M162.007, M162.009 | Private theorems of this module (table above) |

Modifications by Worker 173 on 13 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the U012 Statements and U011 Proofs imports;
- the theorem's type is the statement constant
  `relNorm_eq_pow_inertiaDeg_of_isSeparableStatement R S P p` instead of the
  equation it unfolds to;
- the anonymous local instances M162.001 and M162.008 are replaced by the
  local instance attribute on `FractionRing.liftAlgebra`, as in the statement
  module; each source use of them is a term
  `FractionRing.liftAlgebra R (FractionRing S)`, which is what instance
  synthesis now produces;
- the section variable `[IsIntegrallyClosed R]` and the `omit … in` commands
  are dropped. The source omits it for M162.007, and M162.002 and M162.004 do
  not mention `R` or `S`. M162.007 keeps `[IsIntegrallyClosed S]` as in the
  source, now as a section variable;
- the U011 helpers M162.003, M162.005 and M162.006, the M162.011 theorem
  (imported instead) and every declaration after line 319 are omitted.

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
the imported statement and proof modules and their paired Markdown remain
frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are byte-identical to the
retained originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This module proves only M162.012. The local-field specialization M162.016,
which applies this theorem to valuation integer rings, is a separate proof.
