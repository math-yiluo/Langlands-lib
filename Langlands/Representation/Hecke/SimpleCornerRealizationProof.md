# Realization of simple Hecke corner modules

Author: Worker 136. The theorem
`Langlands.Hecke.simpleCornerModuleRealization.{u,v}` proves exactly the published
`SimpleCornerModuleRealizationStatement.{u,v}`. For every simple module over the
actual compact-open Hecke corner, it produces an irreducible smooth complex
representation in carrier universe `max u v` whose actual `K`-fixed space is
linearly equivalent to that module over the same corner. There are no extra
premises, and the group and module universes remain independent.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.1.5 Theorem (iii), printed p.61 / PDF p.67, with
the setup on printed p.60 / PDF p.66. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read these pages. Renard obtains this assertion from the general
idempotent-corner correspondence of I.3.2 and the equivalence of III.1.4.

The proof applies the reduction in
[SimpleCornerRealizationReduction](SimpleCornerRealizationReduction.md).
Its three premises are discharged by the published theorems
`Algebra.NonUnitalModuleCornerSimpleProof.simpleInducedQuotient`,
`Algebra.NonUnitalModuleCornerSimpleProof.fixedPartInducedQuotient`, and
`Hecke.heckeNondegenerateModuleEquivalence`. The first two are used at universes
`u,v`, and the last at `u,max u v`.

Concretely, transport the given module to the abstract corner of the normalized
indicator idempotent, form its simple induced annihilator quotient, and use the
Hecke-module equivalence to realize that quotient as an integrated smooth
representation. Simplicity gives irreducibility. The normalized indicator
identifies the representation's `K`-fixed vectors with the idempotent fixed part;
the general corner comparison identifies that part with the original module.
The reduction's paired explanation gives the constituent maps and their
linearity argument.
