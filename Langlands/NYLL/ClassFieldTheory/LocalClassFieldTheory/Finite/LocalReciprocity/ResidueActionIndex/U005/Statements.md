# Index of the degree image of a subgroup with a finite residue image: statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phase of source row
M244.005:

- `residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroupStatement`,
  for the source theorem
  `residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It has no proof here. A later proof will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup`.

## The proposition

```lean
set_option linter.unusedVariables false in
def residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroupStatement :
    Prop :=
  ∀ (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    {G : Type*} [Group G]
    (rho : G →* (Omega ≃ₐ[k] Omega))
    (H : Subgroup G)
    (E : FiniteGaloisIntermediateField k Omega)
    (himage : H.map rho = E.toIntermediateField.fixingSubgroup),
    (H.map ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
      Module.finrank k E
```

The binders are as follows:

- `k` is a finite field (`[Field k] [Fintype k]`) and `Omega` is a field
  with a `k`-algebra structure that is algebraic over `k` and algebraically
  closed. So `Omega` is an algebraic closure of `k`. Both are in `Type`
  (universe `0`), as in the source section variables.
- `G` is an arbitrary group, implicit, in an arbitrary universe. Its
  `Type*` binder gives the definition its only universe parameter, `u_1`, as
  for the source theorem.
- `rho : G →* (Omega ≃ₐ[k] Omega)` is any group homomorphism from `G` to the
  Galois group of `Omega` over `k`. In the source it is applied to the
  residue action of a decomposition group.
- `H` is a subgroup of `G`.
- `E` is a finite Galois intermediate field of `Omega / k`, Mathlib's
  `FiniteGaloisIntermediateField k Omega`.
- `himage` says that the image `H.map rho` of `H` is the fixing subgroup
  `E.toIntermediateField.fixingSubgroup`, Mathlib's subgroup of
  automorphisms of `Omega` over `k` that fix every element of `E`.

`residueAbsoluteDegreeIn k Omega : (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul` is the
published intrinsic residue degree (source row M236.017): the inverse of the
arithmetic Frobenius isomorphism from `ZHatMul`, the profinite integers
written multiplicatively, to the Galois group. It sends an automorphism to its
Frobenius exponent. `.toMonoidHom.comp rho` is the composite homomorphism from
`G` to `ZHatMul`.

The conclusion says that the image of `H` under this composite, a subgroup
of `ZHatMul`, has `Subgroup.index` equal to `Module.finrank k E`, the degree
`[E : k]`. Here `E` is used as a type through Mathlib's coercion of a
`FiniteGaloisIntermediateField` to the type of its intermediate field, with
the `k`-module structure of that intermediate field. `Subgroup.index` is a
natural number, defined to be `0` for infinite index. Since `E / k` is
finite, `[E : k]` is a positive natural number, so the proposition says
that this index is finite and equals the degree.

Mathematically this follows because the residue degree map is a group
isomorphism: the image of `H` is the image of the fixing subgroup of `E`,
whose index in the Galois group is `[E : k]` by Galois theory. The source
proof (lines 104–108) instead goes through the source residue datum
`residueDatumIn` (M238.001) and the source theorem
`Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup` (M238.004).
Neither is needed by the proposition.

### Binders that come from the section variables

The source theorem is declared in the section `FiniteImageIndex`
(lines 87–110) with the section variables
`(k Omega : Type) [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
[Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]` (lines 89–91). Lean adds
to a theorem the section variables that its signature mentions, here `k`
and `Omega`, and every section instance variable whose type mentions only
included variables. All six instance binders mention only `k` and `Omega`,
so the source theorem takes all of them, in this order, before its own
binders. A private probe confirms this. It declares a theorem under the same
section variables, and `#check` shows that it takes all six instance
binders. The binders are also needed: `residueAbsoluteDegreeIn k Omega`
takes exactly these six instances (M236.017 Markdown, “Parameters of both
definitions”). The proposition therefore has them as its leading universal
binders, with the source binder kinds (`k` and `Omega` explicit).

### The unused hypothesis name

The conclusion does not mention `himage`, but the source names this
hypothesis and the source proof uses it (`rw [← Subgroup.map_map, himage]`).
The proposition keeps the name, which documents the hypothesis and allows
a proof to use the source text. Lean's unused-variables linter would warn
about the named binder, so the definition is preceded by
`set_option linter.unusedVariables false in`. As a `∀` binder the name does
not change the proposition.

A private probe, under the source section variables, proves a theorem with
the source signature (with `G : Type`, and again with `G` in an arbitrary
universe `u`) from a hypothesis `hS` of the proposition by the term
`hS k Omega rho H E himage`. So the source signature, elaborated in the
source context, is an instance of this proposition. Checked with the
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean reports for the
definition: kind `definition`, the single universe parameter `u_1`, a
`Prop`-valued statement, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M236.017, `LocalClassFieldTheory.residueAbsoluteDegreeIn` | `Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteDegreeIn` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions`) |

`ZHatMul` (`Langlands.NYLL.ClassFormation.ZHatMul`, the abbreviation
`Multiplicative ZHat`, module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`)
occurs only through the type of `residueAbsoluteDegreeIn` and is imported
through its module. `FiniteGaloisIntermediateField`,
`IntermediateField.fixingSubgroup`, `Subgroup.map`, `Subgroup.index`,
`ContinuousMonoidHom.toMonoidHom`, `MonoidHom.comp` and `Module.finrank`
are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `7c9e16fc0b3c4040e2c63316beeb78289ddffdb5` was
searched for `residueAbsoluteDegreeIn` and `residueDatumIn`. The only
published declarations that mention them are the M236.016 and M236.017
definitions and the M236.022 statement
`finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement` (module
`...ResidueAlgebraicClosureDegree.Equiv.Statements`). That statement says
that the finite Frobenius coordinate of the restriction of an automorphism
to a finite Galois subextension `E` is the reduction modulo `[E : k]` of its
residue degree. It is not about indices of subgroups. `residueDatumIn` (M238.001) is not yet published. No
published declaration states an index result for subgroups of `ZHatMul`.

Mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index` (module
`Mathlib.FieldTheory.Galois.Basic`) says that for a Galois extension, the
degree of an intermediate field equals the index of its fixing subgroup.
It is about the fixing subgroup in the Galois group. This proposition is
about the image of a subgroup of an arbitrary group `G` under the composite
with the residue degree map into `ZHatMul`. It follows from Mathlib's
theorem and the fact that the residue degree map is an isomorphism, but it
is a different statement.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The M244.005 docstring is lines 93–95 and the signature lines 96–103; the
proof is lines 104–108. The section `FiniteImageIndex` opens at line 87 and
closes at line 110, and its variables are lines 89–91. The header occupies
lines 1–5, the namespace line 22, the `open` lines 24, 26 and 34, the
`noncomputable section` line 30, the `universe` line 32, and the closing
`end` lines 112–113.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M244.005, `LocalClassFieldTheory.residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup` | `Langlands.NYLL.LocalClassFieldTheory.residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroupStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup`, reserved for the proof |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variables `k` and `Omega` and their six instance
  binders become the leading universal binders, in source order and with
  the source binder kinds. The theorem binders `{G : Type*}`, `[Group G]`,
  `rho`, `H`, `E` and `himage` and the conclusion are the source text. The
  proof is omitted for the separate proof phase.
- `set_option linter.unusedVariables false in` is added before the
  definition, because the conclusion does not mention `himage` (see above).
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions`.
- The `noncomputable section`, the `universe u v` line, the `open` lines,
  which this statement does not need, the `section FiniteImageIndex`
  wrapper and all other declarations of the source file are omitted. The
  module docstring is a new short description of this unit.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.005 statement target. Its proof and the
other rows of the source file are not part of this unit.
