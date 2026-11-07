# The group action on the compact-open completion

Author: Worker 1775. Namespaces: `Langlands.CompactCompletion` and
`Langlands.HarishChandraSchwartz.CompactOpenSubgroup`.

This is derived infrastructure for the completion model of Renard 2026,
I.1.4–I.1.5 (printed pp.9–10 / PDF pp.15–16) and VI.9.7 (printed
pp.205–206 / PDF pp.211–212). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source uses the action on the completion and its subgroup invariants.
This module verifies that the published formula for that action preserves
the actual compact-open compatible-family space.

Let `G` be a topological group and `ρ` a smooth complex representation on
`V`, with independent group and carrier universes. No local compactness,
admissibility or existence of compact open subgroups is assumed.

The compact-open subgroup lemmas give the membership rule for conjugation,
its identity, composition and order laws, and the equality with the
`Jacquet.conjOpenSubgroup` construction. The latter equality allows reuse
of the existing conjugation law for normalized compact averages.
`averageMap_translate` states

`e_K(ρ(g)v) = ρ(g)e_{g⁻¹Kg}(v)`.

The proof applies `Jacquet.averageMap_conj` to `g⁻¹Kg` and identifies its
conjugate by `g` with `K`. Hence `translate_mem` proves that

`(g · x)_K = ρ(g)x_{g⁻¹Kg}`

is compatible whenever `x` is. The family identity and composition laws
follow from the corresponding representation and conjugation laws.

`action ρ hρ g` is the resulting complex-linear endomorphism of the
completion. `action_one` and `action_mul` give its identity and composition
laws, and `representation ρ hρ` packages them as a group representation.
`action_apply` and `representation_apply` expose the displayed component
formula. `actionEquiv ρ hρ g` is its linear automorphism, whose inverse is
translation by `g⁻¹`; `actionEquiv_apply` and `actionEquiv_symm_apply`
give both component formulas. Smoothness of the completion representation
is not claimed.

`completionFixed_eq_fixedVectors` identifies the previously defined
`completionFixed ρ hρ H` with the `H`-fixed vectors of this representation,
for every subgroup `H`. This follows directly by expanding the action
and the two definitions of fixedness.

This supplies the action and invariant-space interpretation used in
VI.9.7. It does not identify the stable-image limit with the radical-fixed
completion, establish the specific parabolic cofinality or prove either
exact target of the task.
