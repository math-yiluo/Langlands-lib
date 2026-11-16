# Abstract fixed-field relative norm: value equality

This module proves
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGalois`
with type
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement K H hH x`.
It uses the published proposition in the adjacent `U006.Statements` module
without changing that proposition or its dependencies.

## Exact scope

The complete telescope is

```lean
(K : Type) [Field K]
(H : ClosedSubgroup (intrinsicAbsoluteGalois K))
(hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
[Finite ((intrinsicAbstractBase K).toSubgroup ⧸
  extensionSubgroup (intrinsicAbstractBase K) H hH)]
[FiniteDimensional K
  (abstractFixedField K (SeparableClosure K) H)]
[IsGalois K (abstractFixedField K (SeparableClosure K) H)]
(x : (abstractFixedField K (SeparableClosure K) H)ˣ)
```

The field has universe zero. Set
`E := abstractFixedField K (SeparableClosure K) H`, the actual intermediate
fixed field of `H`. The theorem compares the class-formation relative norm
of the fixed coefficient corresponding to `Additive.ofMul x` with the
ordinary field norm `Algebra.norm K (x : E)`. After projecting the relative
norm to its ambient additive unit, applying `Additive.toMul`, and coercing
the unit to `SeparableClosure K`, its value is
`algebraMap K (SeparableClosure K) (Algebra.norm K (x : E))`.
The theorem requires precisely the displayed hypotheses. In particular,
it does not require a local-field structure.

## Implemented proof

After unfolding the target proposition, the proof follows the pinned
source argument.

1. Let `y` be the fixed coefficient for `H` obtained from
   `abstractFixedFieldUnitsEquivGaloisFixed`, and let `yE` be the coefficient
   for the closed fixing subgroup of `E` obtained from
   `intermediateFieldUnitsEquivGaloisFixed`. The two published coercion
   theorems identify `yE.1` with `y.1`: both are the ambient unit induced by
   the same inclusion of `E` into `SeparableClosure K`.
2. Apply
   `relativeNorm_intermediateFieldUnit_val_of_isSeparable K (SeparableClosure K) E x`.
   The finite-dimensional and Galois instances on `E/K` supply its finite
   separable hypotheses. The separable closure has the required Galois and
   separably closed instances. This gives the ordinary field-norm value
   for the relative norm indexed by the closed fixing subgroup of `E`.
3. Apply `relativeNorm_coe_eq_of_closedSubgroup_eq` with both base subgroups
   equal to `intrinsicAbstractBase K`, the other subgroups equal to the
   closed fixing subgroup of `E` and `H`, and coefficients `yE` and `y`.
   The base equality is reflexivity;
   `closedFixingSubgroup_abstractFixedField_eq` supplies the other subgroup
   equality. The published finite-separable intermediate-field
   infrastructure supplies the finite quotient instance for the fixing
   subgroup; the target supplies the finite quotient instance for `H`.
   The coefficient equality from step 1 completes the transport.
4. Apply `congrArg` to that equality with the map from an ambient additive
   unit to its underlying field element. Its symmetry, followed by the
   equality from step 2, proves the target.

`intrinsicAbsoluteUnits K` and `intrinsicAbstractBase K` unfold to the
published Galois ambient-unit representation and bottom-field fixing
subgroup used by the intermediate-field theorem. No additional norm,
fixed-field, or coefficient construction is introduced.

## Published inputs

All names below are in `Langlands.NYLL.LocalClassFieldTheory`.

| Declaration | Imported module after `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.` |
| --- | --- |
| `relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement` | `Existence.NormSubgroupOrderEmbedding.U006.Statements` |
| `relativeNorm_intermediateFieldUnit_val_of_isSeparable` | `LocalReciprocity.SeparableFixedFieldNorm.U009.Proofs` |
| `relativeNorm_coe_eq_of_closedSubgroup_eq` | `LocalReciprocity.AbstractFixedFieldNorm.U001.Proofs` |
| `intermediateFieldUnitsEquivGaloisFixed_coe` | `LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.U007.Proofs` |
| `abstractFixedFieldUnitsEquivGaloisFixed_coe` | `LocalReciprocity.AbstractFixedFieldUnits.Initial.U002.Proofs` |
| `closedFixingSubgroup_abstractFixedField_eq` | `LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs` |

The existing modules also supply the actual fixed-field unit equivalences,
the intrinsic objects, the relative norm, and the requisite finite quotient
instance. Mathlib supplies `SeparableClosure`, `Algebra.norm`, and the
canonical field, algebra, and separability instances. This module adds one
theorem and no instances.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
M300.006, lines 149–197 (signature 149–166; proof 167–197), with section
parameters at line 32. The readable source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
Its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The source declaration
`LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGalois`
becomes
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGalois`.
Worker 537 made these adaptations:

1. Add the `Langlands.NYLL` namespace prefix and make the source section
   binders `(K : Type) [Field K]` explicit, preserving their order and the
   remaining telescope.
2. State the conclusion as the published target applied to all source
   parameters, then unfold that target. The following tactic proof is
   unchanged from the source.
3. Use the six focused imports listed above, omit unrelated declarations
   and unused namespace openings, and replace the module documentation
   and theorem docstring with descriptions of this focused proof.

The original copyright and author header is retained verbatim. The
Apache-2.0 license and original notices remain in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`. Their respective SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
