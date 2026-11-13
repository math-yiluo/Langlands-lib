# NYLL M010: residue degree equals degree for unramified finite field extensions

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.138 | `ClassFormation.FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` | 1288–1294 | `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramifiedStatement` |

The target keeps the source telescope exactly. It takes implicit
`{G : Type u}` with `[Group G] [TopologicalSpace G]` from the section variable
(source line 46) and universe `u` (source line 30). Its explicit arguments are,
in source order, `(E : FiniteAbstractFieldExtension G)`, `(D : DegreeData G)`
and the hypothesis `(hE : E.IsUnramified D)`. Its body is the source
conclusion `(E.residueDegree D : ℕ) = (E.degree : ℕ)`, an equation of natural
numbers obtained by coercing two positive naturals.

It says the following. Let `E` be a finite extension between two fields that
are finite over the distinguished base (M010.130). Suppose `E` is unramified
for the degree datum `D` (M010.133): for the underlying extension with top
field `E.field.field` and base `E.base.field`, the inertia part
`E.base.field.toSubgroup ⊓ D.degree.toMonoidHom.ker` is contained in
`E.field.field.toSubgroup`. Then the positive relative residue degree of `E`
(M010.136) equals the positive degree of `E` (M010.135), the `Nat.card` of
the relative coset type `E.base.field.toSubgroup ⧸ E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup`.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.residueDegree`
(M010.136), from the only import, module
`Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions`; and,
through it, `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension`
(M010.130), its `IsUnramified` (M010.133) and `degree` (M010.135), from module
`Degree.Fields.FiniteAbstractField.Extension.Definitions`, and
`Langlands.NYLL.ClassFormation.DegreeData`. Module names here are
abbreviated; each full name has the prefix
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.`.

Modifications by Worker 171: the source theorem is converted to
`def residueDegree_eq_degree_of_isUnramifiedStatement (E : FiniteAbstractFieldExtension G) (D : DegreeData G) (hE : E.IsUnramified D) : Prop := (E.residueDegree D : ℕ) = (E.degree : ℕ)`.
Proofs of the target are a separate proof task, so the source proof is
omitted. That proof is the term
`E.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified D hE`,
the corresponding source theorem for finite abstract extensions. The
namespace is prefixed with `Langlands.NYLL`.

The hypothesis `hE` is never mentioned in the conclusion, so Lean's
unused-variables linter would warn about it. The Lean file keeps the source
name `hE` and turns that linter off for this one declaration with
`set_option linter.unusedVariables false in`. The option affects only
linting of this declaration, not its meaning. A proof of the statement
receives `hE` as an argument, as in the source theorem.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
