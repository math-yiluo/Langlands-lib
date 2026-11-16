# NYLL M053.001: the Frobenius exponent is additive

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusExponent_mulStatement`
by the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusExponent_mul`.
The theorem's type is exactly that proposition applied to its source
parameters, `frobeniusExponent_mulStatement D K L hLK σ₁ σ₂`. It has the
single universe parameter `u` of the group `G`.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusExponentMul.Statements`
(the target) and the published proof module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U001.Proofs`
of M009.001 `proCIntegerOne_pow_nat_injective`. The statement's
Lean/Markdown pair and its complete imported chain remain unchanged.

## Target and parameters

The theorem has, in this order, the explicit `D : DegreeData G`, the
explicit `K : FiniteResidueAbstractField D`, `L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instance-implicit normality
hypothesis `[hLnormal : (extensionSubgroup K.field L hLK).Normal]`, and two
explicit Frobenius elements `σ₁ σ₂ : D.FrobeniusElements K L hLK`; the
section variables are `{G : Type u} [Group G] [TopologicalSpace G]`.

A Frobenius element is a class `σ` of
`K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` together with
a proof of `∃ n, 0 < n ∧ D.extensionNormalizedDegree K L hLK σ = ofAdd 1 ^ n`.
Its exponent `D.frobeniusExponent K L hLK σ` is `Exists.choose σ.2`, and the
semigroup product of the published `frobeniusMul` has underlying class
`σ₁.1 * σ₂.1`. Unfolding the target gives

`D.frobeniusExponent K L hLK (σ₁ * σ₂) =
  D.frobeniusExponent K L hLK σ₁ + D.frobeniusExponent K L hLK σ₂`.

## Implemented proof

The file first proves a private auxiliary lemma

```lean
private theorem frobeniusExponent_mul_normalizedDegree_eq_pow (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK σ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).2
```

which is the statement and source proof of the unpublished M014.014
`extensionNormalizedDegree_frobenius_eq_pow`: the chosen exponent satisfies
the second conjunct of the defining existential. Its normality binder is
written as `L.toSubgroup.subgroupOf K.field.toSubgroup`, the body of the
abbreviation `extensionSubgroup`, as in the published definitions of
`FrobeniusElements` and `frobeniusExponent`.

The main proof is the source calc chain:

1. `apply proCIntegerOne_pow_nat_injective` reduces the equality of natural
   numbers to the equality of the powers `ofAdd (1 : ZHat) ^ _` in
   `Multiplicative ZHat`: distinct natural powers of the generator are
   distinct (published M009.001).
2. The power with exponent `frobeniusExponent (σ₁ * σ₂)` is
   `extensionNormalizedDegree (σ₁ * σ₂).1`, by the auxiliary lemma (read
   backwards).
3. `show` rewrites `(σ₁ * σ₂).1` to `σ₁.1 * σ₂.1`, which holds by definition
   of the published `frobeniusMul`; then `map_mul` for the monoid
   homomorphism `extensionNormalizedDegree K L hLK` splits the product.
4. Rewriting twice with the auxiliary lemma turns the two degrees into
   `ofAdd 1 ^ frobeniusExponent σ₁` and `ofAdd 1 ^ frobeniusExponent σ₂`.
5. Mathlib's `pow_add` combines them into
   `ofAdd 1 ^ (frobeniusExponent σ₁ + frobeniusExponent σ₂)`.

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **M014.014.** The two source citations of
  `D.extensionNormalizedDegree_frobenius_eq_pow` (calc steps one and three)
  are replaced by the private lemma above, whose proof term is the source
  proof (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`,
  lines 318–327). Its private name does not conflict with the adapted name
  of M014.014, which this module does not declare.
- **M015.003.** The source step `rw [frobeniusMul_coe, map_mul]` rewrites
  with the unpublished `frobeniusMul_coe : (σ * τ).1 = σ.1 * τ.1`, whose
  source proof is `rfl`
  (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`,
  lines 56–65). The port uses the definitional `show` instead, followed by
  `rw [map_mul]`.
- The `@[simp]` attribute of the source theorem is not used, since the
  published target is a definition of a proposition.
- `open CyclicCohomology` makes `extensionSubgroup` available, as in the
  statement module.

## Actual dependencies

- The published proposition `DegreeData.frobeniusExponent_mulStatement`
  (unfolded only) in `Reciprocity/Construction/MainMultiplicativity/FrobeniusExponentMul/Statements`.
- The published definitions `DegreeData.FrobeniusElements` and
  `DegreeData.extensionNormalizedDegree` (`Degree/FrobeniusLift/FrobeniusElements/Definitions`),
  `DegreeData.frobeniusExponent` (`Degree/FrobeniusFixedField/FrobeniusClosure/Definitions`)
  and the multiplication instance `DegreeData.frobeniusElementsMul` built
  from `DegreeData.frobeniusMul` (`Reciprocity/Construction/FrobeniusSemigroup/Definitions`),
  reached through the unchanged import chain.
- The published theorem `Langlands.NYLL.ClassFormation.proCIntegerOne_pow_nat_injective`
  (M009.001) in `GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U001/Proofs`.
- Mathlib's `Exists.choose_spec`, `map_mul`, `pow_add` and
  `Multiplicative.ofAdd`.

The unpublished M014.014 and M015.003 are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean:37–67`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean#L37-L67).
Lines 37–38 are the docstring, 39 the `@[simp]` attribute, 40–47 the
signature and conclusion, and 48–67 the tactic proof retained above (the
partition's unit M053.001 spans lines 40–84, up to the next declaration).
The enclosing context is `universe u` (line 20), `namespace ClassFormation`
(line 22), `open KummerTheory` and `open CyclicCohomology` (lines 24–25),
`noncomputable section` (line 27), `section frobeniusAlgebra` with
`variable {G : Type u} [Group G] [TopologicalSpace G]` (lines 31–33) and
`namespace DegreeData` (line 35). The whole-file SHA-256 values of the
retained snapshot files, recomputed by Worker 746 on 16 November 2026 UTC,
are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean` | `913562295296948d960ad31a3f03b201046ba2089b481705109cd238619c3445` |
| `Degree/FrobeniusFixedField.lean` | `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3` |
| `Reciprocity/Construction/FrobeniusSemigroup.lean` | `d11fc29514c9a12171d2a10287d09d10aa13b765641c57893c102aa7a6a70a06` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `DegreeData.frobeniusExponent_mul` (M053.001) | Published `DegreeData.frobeniusExponent_mulStatement` |
| Proof `DegreeData.frobeniusExponent_mul` | This theorem of the same adapted name in `FrobeniusExponentMul/U001/Proofs` |
| `D.extensionNormalizedDegree_frobenius_eq_pow` (M014.014) | Private `frobeniusExponent_mul_normalizedDegree_eq_pow`, same proof term |
| `frobeniusMul_coe` (M015.003) | Definitional `show` |
| `proCIntegerOne_pow_nat_injective` (M009.001) | Published theorem of the same adapted name |

The [public partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m053)
places this proof at M053.001, first in its module.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 746's dated modification
record. Worker 746 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M053.001. The published proofs of M014.014 and
M015.003, the rest of M053 and any reciprocity theorem are separate work.
