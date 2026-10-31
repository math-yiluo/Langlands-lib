# Extension compatibility of the canonical complete-DVF packages: proof

This module proves the closed proposition
`Langlands.NYLL.LocalFieldTheory.LocalCompleteDVFValuationHasExtensionStatement`
(NYLL M248.002), published in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ExtensionStatement`.
The proof adapts the proof of M248.002,
`LocalFieldTheory.localCompleteDVFValuation_hasExtension`, from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`, lines 57–74](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L57-L74),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source signature is
lines 59–66 and the tactic proof is lines 67–74.

| Theorem | Universe parameters | Complete unapplied type |
| --- | --- | --- |
| `Langlands.NYLL.LocalFieldTheory.localCompleteDVFValuation_hasExtension` | `u, v` | `LocalCompleteDVFValuationHasExtensionStatement.{u, v}` |

The theorem's type is the named target constant itself, at its own universe
parameters `u` and `v` in order, with no further arguments. The two levels stay
independent: `K` lies in `Type u` and `L` in `Type v`. The module contains no
other declaration and no instance.

## The target

The target quantifies over `(K : Type u) (L : Type v) [Field K] [Field L]
[Algebra K L]`, a supplied valuative relation, topology and
`IsNonarchimedeanLocalField` structure on each of `K` and `L`, and the instance
premise `Valuation.HasExtension (ValuativeRel.valuation K)
(ValuativeRel.valuation L)`. It concludes
`Valuation.HasExtension (localCompleteDVF K).valuation
(localCompleteDVF L).valuation`. Here `localCompleteDVF` is the published
M248.001 package. Both the premise and the conclusion use the supplied
`algebraMap K L`.

`vR.HasExtension vA` is Mathlib's class with the single field
`val_isEquiv_comap : vR.IsEquiv (vA.comap (algebraMap R A))`. It asks that the
base valuation be equivalent to the pullback of the upstairs valuation along
the algebra map. It does not ask for equal values.

## The proof

The proof is the source tactic proof, run after the target's binders are
introduced.

1. `intro K L _ _ _ _ _ _ _ _ _ _` introduces the two fields and the ten
   instance arguments in target order. The last of these is the premise
   `Valuation.HasExtension (ValuativeRel.valuation K)
   (ValuativeRel.valuation L)`, which becomes a local instance.
2. `apply Valuation.HasExtension.ofComapInteger` uses Mathlib's lemma
   `Valuation.HasExtension.ofComapInteger`
   (`Mathlib/RingTheory/Valuation/Extension.lean`, line 112). For a field `K`,
   a `K`-algebra `A`, a valuation `vK` on `K` and a valuation `vA` on `A`, it
   derives `vK.HasExtension vA` from the equality of subrings
   `vA.integer.comap (algebraMap K A) = vK.integer`. With
   `vK = (localCompleteDVF K).valuation` and
   `vA = (localCompleteDVF L).valuation`, the remaining goal says: the
   pullback along `algebraMap K L` of the valuation integers of the package of
   `L` equals the valuation integers of the package of `K`.
3. `ext x` reduces this equality of subrings to: for `x : K`,
   `x` lies in the pullback if and only if `x` lies in the integers of the
   package of `K`.
4. `change` restates this goal as
   `ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
   ValuativeRel.valuation K x ≤ 1`. Lean accepts it because the two goals are
   definitionally equal:
   - membership in `Subring.comap f S` is membership of `f x` in `S`, and
     membership in `v.integer` is `v y ≤ 1`;
   - `localCompleteDVF K` is built with the published M247.004 constructor
     `completeDVFOfCompleteValuedField`. That constructor stores
     `ValueGroup := ValuativeRel.ValueGroupWithZero K` with its canonical
     ordered structure, and `valuation := Valued.v`. Under Mathlib's
     `Valued K (ValuativeRel.ValueGroupWithZero K)` instance, `Valued.v` is
     `ValuativeRel.valuation K` by definition. So the projection
     `(localCompleteDVF K).valuation` unfolds to `ValuativeRel.valuation K`,
     and the order and `1` of the stored value group are the canonical ones.
     The same holds for `L`.

   The published M248.001 Markdown records the corresponding `rfl` checks.
5. `exact Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation K)
   (ValuativeRel.valuation L) x` closes the goal. This is Mathlib's lemma
   (`Mathlib/RingTheory/Valuation/Extension.lean`, line 85):
   `vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1` whenever `vR.HasExtension vA`. Its
   `HasExtension` instance is the introduced premise for the canonical
   valuations of `K` and `L`.

Mathematically: the integers of the canonical package of a local field are the
elements of canonical valuation at most `1`. Since the canonical valuation of
`L` extends that of `K` along `algebraMap K L`, an element `x` of `K` has
`v_K(x) ≤ 1` exactly when its image has `v_L(x) ≤ 1`. For a field, equality of
the integer subrings is enough to give an extension of valuations.

The premise is used only in step 5. The proof uses no finiteness,
separability, uniformity, completeness, integral-closure or finite-module fact.
It uses no global instance, no integer-ring comparison and no reciprocity
result.

## Source correspondence and modifications

The source proof, lines 67–74, is

```
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
  exact
    Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) x
```

The adapted proof makes only these changes:

- The source theorem takes its arguments as theorem binders. The adapted
  theorem has the closed target `LocalCompleteDVFValuationHasExtensionStatement.{u, v}`
  as its type, so the proof begins with `intro` for the same binders in the
  same order.
- `Valuation.HasExtension.ofComapInteger` and
  `Valuation.HasExtension.val_map_le_one_iff` are written with `_root_.`,
  because the declaration lives in the `Langlands.NYLL` namespace. They are the
  same Mathlib lemmas.
- The namespace is prefixed with `Langlands.NYLL`. The theorem name and
  docstring are those of the source.
- The original imports are replaced by the single published statement module,
  which itself imports `Mathlib.RingTheory.Valuation.Extension` and the
  published M248.001 module `...FiniteExtensionCompleteDVF.Canonical`.

The source file's later units are not adapted here. These are comparison of
rings of integers with the integral closure, the finite-module theorem, chosen
extension data and its instance, and uniqueness of the extension.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a theorem with level parameters `u, v`. It
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The
published target pair `ExtensionStatement.lean`/`.md` and its imports are
unchanged. These checks establish compilation. Exact-target validation,
semantic review and publication are separate steps.

## Attribution

The original file's SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-specific errata directory exists in the workspace, project notes or
Library.

The original copyright and author header is retained verbatim. The inherited,
unmodified [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values
are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE has no entry for the selected source file.

On 30 October 2026, Worker 785 adapted the proof with the changes listed
above and wrote this explanation. Worker 106 supplied routing only. No
unpublished implementation or draft from another worker was reused.
