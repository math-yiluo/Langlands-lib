# Subgroup, quotient-image and transported filtration data

This module extracts four data constructions from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Quotient.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Quotient.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The complete original
file has SHA-256
`7055997b7d600c1ed8e846d9d30222f8d8d670902f4e33566e9857ce686742b6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable NYLL erratum was found in the supplied Library or workspace
errata notes.

## Exact source correspondence

Let `S` denote the original namespace
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`
and `T` denote
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
The four complete source declarations are mapped as follows.

| Source declaration | Original lines / unit | Adapted declaration |
| --- | --- | --- |
| `S.subgroupFiltration` | 39–45 / M314.001 | `T.subgroupFiltration` |
| `S.quotientImageFiltration` | 63–71 / M314.004 | `T.quotientImageFiltration` |
| `S.transportEquiv` | 157–163 / M314.010 | `T.transportEquiv` |
| `S.quotientImageTransport` | 231–234 / M314.017 | `T.quotientImageTransport` |

The module imports the actual published
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`
from
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration`.
This bundle has fields `lower : ℕ → Subgroup G`, normality of every lower
subgroup, and antitonicity: `m ≤ n` implies `lower n ≤ lower m`.
No replacement filtration structure is introduced.

## Interfaces and mathematical meaning

With namespace `T` open, the complete interfaces are:

```lean
subgroupFiltration.{u}
    {G : Type u} [Group G]
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) :
    AntitoneNormalSubgroupFiltration H

quotientImageFiltration.{u}
    {G : Type u} [Group G]
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal] :
    AntitoneNormalSubgroupFiltration (G ⧸ H)

transportEquiv.{u, v}
    {G : Type u} [Group G] {G' : Type v} [Group G']
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') :
    AntitoneNormalSubgroupFiltration G'

quotientImageTransport.{u, v}
    {G : Type u} [Group G] {G' : Type v} [Group G']
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') :
    AntitoneNormalSubgroupFiltration G'
```

The group types are implicit; their group structures and the indicated normality
proofs are instance arguments. The filtration, subgroup and equivalence arguments
are explicit and occur in the source order. The universes `u` and `v` are
independent. The first two definitions have only the original ambient-group
parameters; `G'` and its group structure enter the section before the last two.
None of these definitions requires `Finite`, `Fintype`, a field or a valuation.
The inherited `DiscreteValuationField` namespace adds no such hypothesis.

For an arbitrary subgroup `H ≤ G`, `subgroupFiltration F H` has lower term
`(F.lower n).comap H.subtype`. Thus its elements are precisely the elements of
`H` whose underlying elements lie in `F.lower n`: this is the intersection
with the ambient lower subgroup, viewed inside `H`. Normality of `H` in `G`
is not required. Each lower term is normal in `H` because a homomorphism
preimage of a normal subgroup is normal.

For a normal subgroup `H`, `quotientImageFiltration F H` has lower term
`(F.lower n).map (QuotientGroup.mk' H)` in `G ⧸ H`. This is the pointwise
group-theoretic image of the supplied filtration at the same natural index.
Its normality proof uses normality of `F.lower n` and surjectivity of
`QuotientGroup.mk' H`.

For a group equivalence `e : G ≃* G'`, `transportEquiv F e` has lower term
`(F.lower n).comap e.symm.toMonoidHom`. Membership at level `n` in `G'`
therefore means that the inverse image under `e` belongs to `F.lower n`.
The inverse equivalence supplies the homomorphism along which normality is
pulled back.

Finally, `quotientImageTransport F H e` is defined to be
`transportEquiv (quotientImageFiltration F H) e`. Its lower term unfolds to
`((F.lower n).map (QuotientGroup.mk' H)).comap e.symm.toMonoidHom`.
It equips any isomorphic model `G'` of the quotient with the quotient-image
filtration, using the supplied equivalence.

## Constructor proofs and modifications

All four definition binders and bodies are retained verbatim after the namespace
prefix change. In the subgroup and equivalence constructions, `lower_normal`
uses `(F.lower_normal n).comap` along the specified homomorphism.
In the quotient construction it uses `(F.lower_normal n).map` together with
`QuotientGroup.mk'_surjective H`. Their `antitone` proofs introduce
`m`, `n` and `hmn : m ≤ n`, then apply `Subgroup.comap_mono` or
`Subgroup.map_mono` to `F.antitone hmn`. The composite construction inherits
these laws by applying the two preceding definitions.

Worker 540 extracted exactly these four source commands for Task 6127.
The namespace gains `Langlands.NYLL`; the generic filtration is imported from
its published Library module instead of through the original Herbrand function
module. `Mathlib.Algebra.Group.Subgroup.Basic` supplies normality under
homomorphism images and preimages; `Mathlib.GroupTheory.QuotientGroup.Defs`
supplies the quotient maps. The original cardinality, index and Herbrand-function
imports are unnecessary for this unit, as is the original `noncomputable
section`, which is omitted. The original declaration documentation is retained.

This unit makes no identification of these group-theoretic images with the
actual lower ramification filtration of a valued-field quotient. That
identification needs the later Herbrand quotient theorem. It also includes no
standalone lower-term equations, cardinality identities or Herbrand-function
compatibility theorems; those are separate source units.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The adapted Lean module records Worker 540's extraction and import modifications.
