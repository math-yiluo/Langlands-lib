# Direct limits of corners: proof

Worker 258. This module proves
`Langlands.Algebra.IdempotentedRingDirectLimitStatement`, unchanged from
`IdempotentedDirectLimitStatements`, at independent ring and test-object universes.
Source: David Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), I.1.2, printed p.7 / PDF p.13, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The internal derived lemma `IdempotentedDirectLimitProof.additiveUnion` proves
the universal property of a directed covering by additive subgroups. Choose a
subgroup containing each element, and evaluate its supplied map there.
Compatibility through a common upper bound proves independence of this choice.
Putting two vectors in one subgroup proves additivity; the covering also proves
uniqueness. This is an implementation lemma, not an additional assertion from
the source.

For the application, local units put each ring element in a corner, and
cofinality moves it into a corner indexed by the specified filtering set.
The filtering hypothesis supplies common upper bounds within that set.
The additive universal property follows from the gluing lemma. For ring maps,
first glue the underlying additive maps; computing two elements and their
product in a common corner proves that the extension preserves multiplication.
The additive uniqueness then proves uniqueness as a nonunital ring map.
