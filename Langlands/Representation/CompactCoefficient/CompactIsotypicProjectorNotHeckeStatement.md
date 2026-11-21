# Hecke realization of the compact isotypic projector

Worker 1222, Task 1222 (`f5d1f399-a1f8-4ab5-a981-90b92abd4857`).
`Langlands.Renard.CompactRepresentation.CompactIsotypicProjectorNotHeckeStatement`
formalizes the obstruction in Renard IV.1.5, the paragraph after the Theorem
and before the Proposition, printed p. 92 (PDF p. 98). The source is David
Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The source defines the operator `π(e_τ)` on a smooth representation by applying
`e_{K,τ}` on a vector fixed by a sufficiently small compact open subgroup `K`.
Its printed remark excludes a single Hecke element realizing this family
without a noncompactness hypothesis. For the trivial compact group, the Hecke
unit acts as this projector on every smooth object, since every simple
representation is trivial. The formal statement corrects the remark by
requiring `G` to be noncompact.

The group is Hausdorff, locally compact, totally disconnected and σ-compact.
Renard assumes unimodularity in IV.1.3, printed p. 89 (PDF p. 95). IV.1.4 adds
σ-compactness and fixes a bi-invariant Haar measure on printed p. 90 (PDF p. 96).
IV.1.5 inherits these hypotheses. Here `μ` is a Haar measure on the Borel
measurable structure, with right invariance given explicitly. `D` is an actual
irreducible smooth complex representation with compactly supported smooth-dual
matrix coefficients. The group and representation carriers have independent
universes.

The proposition uses the published `ProjectionDistribution.projector μ D A`,
the intrinsic projector to the `D`-isotypic summand of each smooth object `A`.
The published `ProjectionDistribution.action_element` computes the action
of the constructed `e_{K,τ}` as this projector applied after the normalized
`K`-average. On a `K`-fixed vector the average is the identity, so this
projector is the source operator `π(e_τ)`. The obstruction quantifies over
actual Hecke functions and their integrated actions on these smooth objects.
