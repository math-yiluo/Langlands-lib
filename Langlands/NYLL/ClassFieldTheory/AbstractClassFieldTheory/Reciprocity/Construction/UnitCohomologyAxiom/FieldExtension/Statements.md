# NYLL M032.011: the field-extension bundle of an unramified cyclic extension is unramified

The paired Lean file gives the Prop-valued target
`Langlands.NYLL.ClassFormation.FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension_isUnramifiedStatement`
for the source theorem
`ClassFormation.FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension_isUnramified`.
The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`,
inventory unit M032.011. The theorem occupies lines 129–134: the docstring
is at 129–130, the signature at 131–133 and the proof `by exact E.unramified`
at 133–134. The file SHA-256 is
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`.
The registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The source context is: `namespace ClassFormation` (line 18),
`noncomputable section` (line 26), the variables of lines 105–107,
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}`, and `namespace
FiniteUnramifiedCyclicExtension` (line 117) with
`variable {K : FiniteAbstractField G}` (line 119).

## The statement

The parameters are, in the source order and with the source binder kinds:

- implicit `G : IntegralRepGroupType`, where `IntegralRepGroupType` is the
  Library's `Langlands.NYLL.IntegralRepGroupType` (M002.001, the alias
  `Type 0`). So `G` is in universe zero, as in the source;
- instance arguments `[Group G]` and `[TopologicalSpace G]`;
- implicit `D : DegreeData G`, a degree datum on `G`;
- implicit `K : FiniteAbstractField G`, a closed subgroup of `G` that is
  finite over the distinguished base (M010.121);
- explicit `E : FiniteUnramifiedCyclicExtension D K`, a finite cyclic
  extension `L | K` together with a proof that it is unramified for `D`
  (M032.009).

The variable `{A : Rep ℤ G}` of line 107 does not occur in the theorem, so
Lean does not add it to the telescope, in the source or here.

The body, which is the source conclusion verbatim, is
`E.toFiniteAbstractFieldExtension.IsUnramified D`. Here
`E.toFiniteAbstractFieldExtension` is M032.010 from the sibling module
`FieldExtension/Definitions.lean`: the `FiniteAbstractFieldExtension` with
top endpoint the field of `E`, base endpoint `K` and the relative finite
quotient of `E`. `IsUnramified` is the Library's
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.IsUnramified`
(M010.133). It unfolds to the structural unramifiedness of the underlying
abstract extension: the intersection of the subgroup of `K` with the kernel
of the degree map of `D` lies in the subgroup of the top field. So the
target says that the unramifiedness carried by `E` is still unramifiedness
after passing to the field-extension bundle. No premise is added.

## Modifications

Worker 5424 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to the name. The `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion. The telescope and
  the conclusion are unchanged, so a proof of the target takes `E` as its
  only explicit argument, as the source theorem does.
- The docstring begins with "Target:", and its wording is otherwise the
  source wording.
- The proof (lines 133–134) is not ported. Proving the target is a
  separate `lean.proof@1` task. The source proof is `exact E.unramified`.
- The opens `KummerTheory`, `CyclicCohomology` and `CategoryTheory`,
  `universe u`, the `Generic` section and the other declarations of the
  source module are omitted, because the statement does not use them.
- The source imports are replaced by the single focused import of the
  sibling module `UnitCohomologyAxiom/FieldExtension/Definitions.lean`. That
  module supplies M032.010 and, through its imports, `FiniteAbstractField`,
  `FiniteAbstractFieldExtension.IsUnramified`, `DegreeData`,
  `FiniteUnramifiedCyclicExtension` and `IntegralRepGroupType`.

A focused `lean_check` of this module, with the declaration inspected,
reports no errors or warnings, `statement_returns_prop: true` and no
universe level parameters.

## Scope

This unit states M032.011 and does not prove it. No host reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
