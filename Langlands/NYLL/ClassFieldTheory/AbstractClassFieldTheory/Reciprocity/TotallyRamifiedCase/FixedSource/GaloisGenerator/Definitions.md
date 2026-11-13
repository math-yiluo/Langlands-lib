# NYLL M084: the finite Galois presentation of a cyclic generator

Worker 224, 13 November 2026.

## Source and exact correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`.
The retained file has SHA-256
`4c8289dbb89fb3459f1248a4cd171f813fdc5e7bcba9e845d8b1929261f40f50`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Source declaration and exact lines | Adapted declaration |
| --- | --- | --- |
| M084.003 | `ClassFormation.FiniteCyclicSubextension.toFiniteGaloisSubextension`, definition 91–96, documentation 89–90 | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.toFiniteGaloisSubextension` |
| M084.004 | `ClassFormation.FiniteCyclicSubextension.galoisGenerator`, definition 99–101, documentation 97–98 | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.galoisGenerator` |

The inventory associates M084.003 with line 90; direct numbering of the
retained file places its `def` command at line 91. M084.003 is included under
Task 5858's same-module prerequisite clause: M084.004 uses it in both its
return type and body.

## Complete telescope and constructions

Both definitions have, in order, implicit `{G : IntegralRepGroupType}`,
instance parameters `[Group G]` and `[TopologicalSpace G]`, implicit
`{K : FiniteAbstractField G}`, and explicit `(E : FiniteCyclicSubextension K)`.
The source's ambient group variable is declared at line 27 and the implicit
base field at line 88. The published `IntegralRepGroupType` abbreviation
means `Type 0`. This restriction is retained even though the underlying
finite cyclic and finite Galois bundles admit other universes.

`toFiniteGaloisSubextension E` has type `FiniteGaloisSubextension K.field`.
Its four fields are exactly `E.field`, `E.below`, `E.normal`, and `E.finite`,
in source order. Thus it retains the actual top closed subgroup, its inclusion
in the base subgroup, normality of the relative subgroup, and finiteness of
the relative quotient, while forgetting the chosen generator and its
generation proof. It introduces no proof obligation or replacement field.

`galoisGenerator E` belongs to the named quotient
`E.toFiniteGaloisSubextension.extensionQuotient`. Its body is exactly
`E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.symm E.generator`.
It uses the inverse of the canonical multiplicative equivalence from the
named finite Galois quotient to the subgroup quotient in which `E.generator`
lives. The actual equivalence and its direction are preserved.

## Dependencies and modifications

The finite cyclic structure is the namespaced adaptation of M032.001.
The finite Galois structure, named quotient, group structure, and comparison
equivalence are the namespaced adaptations of M040.001, M040.004, M040.008,
and M040.010. These definitions reuse those objects and their instances.
They introduce no new instance.

The source namespace is prefixed by `Langlands.NYLL`; both data declarations
remain `def`s with the same binder kinds, order, types, bodies, and four-field
construction. The source's `noncomputable section` is retained. Its broad
`TotallyRamifiedCase.FrobeniusNorms` and `TotallyRamified` imports are replaced
by the finite cyclic and finite Galois data modules and the integral
representation universe module. Unused namespace openings and unrelated
theorems are omitted. The two declarations are placed in the required
`FixedSource/` directory, with the generation target in the paired sibling
`Statements` module.

Worker 5424 handles M032 and Worker 224 handles M084.003–M084.005 under the
agreed Task 5858 division. This unit supplies cyclic Galois data; it asserts
no host class-formation or reciprocity theorem.

## Attribution

The original copyright, license, and author header is retained in Lean,
followed by an explicit modification record. The existing Apache-2.0
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained.
