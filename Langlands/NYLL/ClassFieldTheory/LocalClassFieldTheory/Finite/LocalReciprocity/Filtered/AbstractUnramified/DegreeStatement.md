# Finite abstract-field degree comparison target

Adapted by Worker 291 from Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. This pair defines the proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_degree_eq_abstractFixedField_finrankStatement`.
It supplies the target for a separate proof.

The original declaration is
`LocalClassFieldTheory.finiteAbstractField_degree_eq_abstractFixedField_finrank`,
unit M330.006, in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean:192–230`;
its docstring is at lines 190–191, binders and conclusion at 192–208, and
proof at 209–230. The file SHA-256 is
`095bea2e9d86b74ce22127ea88332ca81fd0433ef86e5e9442bb37363930ca53`.
The readable source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

For the source's universe-zero field `K : Type`, a finite abstract field
`H : Langlands.NYLL.ClassFormation.FiniteAbstractField (Gal(SeparableClosure K/K))`,
and the explicit hypothesis

```lean
(Langlands.NYLL.CyclicCohomology.extensionSubgroup
  (Langlands.NYLL.ClassFormation.baseField (Gal(SeparableClosure K/K)))
  H.field (Langlands.NYLL.ClassFormation.le_baseField H.field)).Normal
```

the target is the natural-number equality

```lean
(H.toFiniteAbstractExtension.degree : ℕ) =
  Module.finrank K
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField
      K (SeparableClosure K) H.field)
```

Both the abstract degree and the fixed field are the published constructions.
The latter is the actual `IntermediateField.fixedField H.field.toSubgroup`
inside `SeparableClosure K`, with its canonical algebra and module over `K`.
No replacement field or assumed degree comparison is introduced.

At source lines 200–206 the conclusion first binds this fixed field as `E`,
then binds instances `FiniteDimensional K E` and `IsGalois K E` using
`abstractFixedField_finiteDimensional` (M099.005) and
`abstractFixedField_isGalois_of_base_normal` (M299.005). The equality at
207–208 uses neither instance value: `Module.finrank` is defined without a
finite-dimensionality argument, and its module here comes from the intermediate
field's algebra. Substituting `E` and reducing the unused instance lets gives
exactly the displayed target. This reduction holds for arbitrary supplied
values of the two instance types, so it does not depend on their constructors.
The full normality hypothesis is retained in the declaration's telescope,
although its body does not use it. Finite-dimensionality and Galoisness of the
fixed field are not assertions of this target.

The published `extensionSubgroup` abbreviation is in
`Langlands.NYLL.CyclicCohomology`, as in the source's `CyclicCohomology`
namespace. The task prose's `Langlands.NYLL.ClassFormation.extensionSubgroup`
spelling is resolved to this existing abbreviation; `baseField` and
`le_baseField` are in `Langlands.NYLL.ClassFormation`. The subgroup expression
and the normality hypothesis are unchanged.

The direct Mathlib correspondence is already visible in source lines 216–230:
the abstract degree is the natural cardinality of the base-extension quotient;
its index is the index of `H.field.toSubgroup`; the closed-subgroup
fixed-field correspondence identifies this with the fixed field's fixing
subgroup index; and that index equals the field's finrank. In the approved
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, the relevant
declarations are `Subgroup.index_eq_card`
(`Mathlib/GroupTheory/Index.lean:348`), `Subgroup.relIndex_top_right`
(same file, line 268), `InfiniteGalois.fixingSubgroup_fixedField`
(`Mathlib/FieldTheory/Galois/Infinite.lean:146`) and
`IntermediateField.finrank_eq_fixingSubgroup_index`
(`Mathlib/FieldTheory/Galois/Basic.lean:678`). The last theorem requires
Galoisness of the ambient extension, available for `SeparableClosure K`;
it does not require either erased fixed-field instance. This records the
source correspondence and prospective proof route; this pair contains no
proof of the target.

Every modification from M330.006 is as follows:

- Prefix the source namespace with `Langlands.NYLL` and append `Statement`
  to the source name.
- Replace the theorem and its proof by a `def` returning `Prop`. Adapt the
  docstring to identify a target.
- Reduce the conclusion's `let E` and the two unused `letI` bindings as
  explained above. Preserve `K : Type`, `[Field K]`, explicit `H`, explicit
  `hnormal` with its full subgroup expression, the natural-number coercion
  of the degree and the equality's orientation.
- Extract this unit alone. Retain `noncomputable section` and the relevant
  `open ClassFormation CyclicCohomology`; omit unrelated source namespace openings,
  scoped notation and all other M330 declarations.
- Replace the original module's broad import list with
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`,
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`,
  `Mathlib.FieldTheory.Galois.Basic` and `Mathlib.FieldTheory.IsSepClosed`.
  These provide the published abstract-field degree, concrete fixed field
  and Mathlib field/Galois infrastructure. In this Mathlib version
  `IsSepClosed.lean:349` defines `SeparableClosure`; importing
  `Mathlib.FieldTheory.SeparableClosure` alone does not provide that name.
  The omitted M099.005 and M299.005 constructors add no hypotheses or
  dependencies to this target.
- Use project Lean 4.34.0 and the approved Mathlib pin above instead of
  upstream Lean 4.35.0-rc2 and Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The original copyright and author header is retained verbatim. The Apache-2.0
license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. The target concerns only this degree equality; other
consumers of the omitted fixed-field instances retain their own construction
and proof obligations.
