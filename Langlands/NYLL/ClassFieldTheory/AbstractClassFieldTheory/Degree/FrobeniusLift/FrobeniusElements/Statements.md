# NYLL M012.006 and M012.013: targets for the factorized normalized degree and Frobenius lifting

This file states, as Prop-valued targets, two theorems of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Source lines (declaration line) | Source theorem after `ClassFormation.DegreeData.` | Target definition |
| --- | --- | --- | --- |
| M012.006 | 92–104 (97) | `extensionNormalizedDegree_mk` | `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree_mkStatement` |
| M012.013 | 177–223 (179) | `frobeniusRestriction_surjective` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction_surjectiveStatement` |

The proofs are separate obligations. They prove theorems named
`Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree_mk` and
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction_surjective`,
whose types are these targets applied to their parameters.

## The objects

`D`, `K`, `L`, `hLK`, `L.toSubgroup.subgroupOf K.field.toSubgroup` (the
source's `extensionSubgroup K.field L hLK`), `extensionInertiaWithin`
(M012.002), `normalizedDegree` (M011.006), `extensionNormalizedDegree`
(M012.005), `FrobeniusElements` (M012.009) and `frobeniusRestriction`
(M012.010) are the published source definitions described in the sibling
module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`.

## Statements

Both targets have the source section's implicit `G : Type u` with
`[Group G]` and `[TopologicalSpace G]`, then the source binders in source
order, with `extensionSubgroup K.field L hLK` expanded to
`L.toSubgroup.subgroupOf K.field.toSubgroup`.

- **M012.006.** For `D`, `K`, `L`, `hLK`, the normality instance `hLnormal`
  and `k : K.field.toSubgroup`,
  `extensionNormalizedDegree_mkStatement D K L hLK k` is
  `D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) = D.normalizedDegree K k`.
  The factorized degree of a class is the normalized degree of any
  representative. The source proves it by `rfl` and marks it `@[simp]`. A
  `Statement` definition cannot carry that attribute, and the proof task
  decides whether to add it to the theorem.
- **M012.013, the finite degree-quotient decomposition.** For `D`, `K`, `L`,
  `hLK`, the normality instance `hLnormal` and the finiteness instance
  `[hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]`,
  `frobeniusRestriction_surjectiveStatement D K L hLK` is
  `Function.Surjective (D.frobeniusRestriction K L hLK)`. For a finite Galois
  extension `L | K`, every element of `G(L|K)` is the restriction of a
  Frobenius element, that is, of a class of normalized degree `n • 1` with
  `n > 0`. The finiteness hypothesis is used only by the proof, so
  `hLfinite` is unused in the conclusion. As in the source, it is kept as a
  named binder, and the unused-variable linter is silenced for this
  definition.

## Modifications

Worker 5264 makes these modifications:

- Convert the two source theorems to Prop-valued definitions whose bodies are
  the source conclusions, append `Statement` to their names, and omit the
  proofs and the `@[simp]` attribute.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL` and
  expand `extensionSubgroup K.field L hLK` to its exact Mathlib body, as in
  the sibling definitions module.
- Keep the source universe and variable declarations and the binder names
  and kinds. The source docstrings are reworded as target descriptions that
  begin with `Target` and keep the source's mathematical content.
- Replace the source import of the whole Frobenius module with the sibling
  definitions module.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained.
