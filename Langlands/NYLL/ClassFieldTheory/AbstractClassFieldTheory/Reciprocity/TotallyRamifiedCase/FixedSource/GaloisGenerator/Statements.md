# NYLL M084: the transported cyclic generator generates

Worker 224, 13 November 2026.

## Source and name map

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`,
unit M084.005. Its documentation is at lines 102–103, its statement at
104–105, and its omitted proof at 106–114. The retained source file has
SHA-256 `4c8289dbb89fb3459f1248a4cd171f813fdc5e7bcba9e845d8b1929261f40f50`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Source declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.FiniteCyclicSubextension.galoisGenerator_generates` | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.galoisGenerator_generatesStatement` |

The sibling [Definitions.md](Definitions.md) records the exact source
correspondence for M084.003 and M084.004, which provide the named quotient
and transported generator used here.

## Exact proposition

The complete ordered telescope is implicit `{G : IntegralRepGroupType}`,
instances `[Group G]` and `[TopologicalSpace G]`, implicit
`{K : FiniteAbstractField G}`, and explicit `(E : FiniteCyclicSubextension K)`.
As in the source context at lines 27 and 88, the ambient group has universe
zero. No topological group assumption is added.

The body is precisely
`∀ x, x ∈ Subgroup.zpowers E.galoisGenerator`.
Here `x` ranges over the actual named finite Galois quotient
`E.toFiniteGaloisSubextension.extensionQuotient`, and `Subgroup.zpowers`
uses its published group instance. Thus every element of that quotient is
an integer power of the transported chosen generator. The cyclicity data
already belongs to `E`; no additional cyclicity hypothesis is inserted.
This file states that proposition without proving it.

## Modifications, reuse, and scope

The source theorem becomes a `def` returning `Prop`, with the suffix
`Statement` and namespace prefix `Langlands.NYLL`. Its binder kinds, order,
universe restriction, objects, and complete conclusion are unchanged.
The source proof, which transports integer powers through the quotient
equivalence, is omitted for a separate proof task.

The broad source imports are replaced by the sibling `GaloisGenerator.Definitions`
module, which reuses the published finite cyclic and finite Galois data.
The source `noncomputable section` is retained; unused namespace openings
and unrelated section variables are omitted. No instance, substitute quotient,
or proof of a host class-formation or reciprocity theorem is introduced.

Worker 5424 handles M032 and Worker 224 handles M084.003–M084.005 under the
agreed Task 5858 division.

## Attribution

The Lean header preserves the original copyright, author, and Apache-2.0
notice and records all modifications. The retained license and attribution
files are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
