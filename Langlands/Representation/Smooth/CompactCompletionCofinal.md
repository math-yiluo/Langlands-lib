# Completion restricted to a cofinal family

Author: Worker 1775. Namespace: `Langlands.CompactCompletion`.

This is derived inverse-limit infrastructure for the published compact-open
completion model. Renard 2026, VI.9.7 (printed pp.205–206 / PDF pp.211–212)
computes completions by a filtering system of idempotents. I.1.4 (printed
p.9 / PDF p.15) defines the underlying completion. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This module supplies the elementary restriction and extension construction
needed when a cofinal family of compact open subgroups has been established.
It asserts no cofinality for any particular parabolic family.

Let `ρ` be a smooth complex representation of a topological group `G`, with
independent group and vector-space universes. For a set `S` of compact open
subgroups, `IsCofinal S` means that every compact open subgroup `K` contains
some `L ∈ S`. `completionOn ρ hρ S` consists of functions `v : S → V`
satisfying `e_K v_L = v_K` whenever `L ≤ K` in `S`, where `e_K` is the
published normalized compact average.

`restrict hρ S` restricts a full completion family to `S`.
Given `hS : IsCofinal S`, `extend hρ S hS` extends a restricted family by

`(extend hρ S hS v)_K = e_K v_L` for any `L ∈ S` with `L ≤ K`.

To prove independence of `L`, the Lean proof chooses a member of `S`
contained in the intersection of two proposed indices. Compatibility of
the family and the absorption law `e_K e_L = e_K` for `L ≤ K` show that the
two averages agree. The same absorption law proves that the extended
family is compatible. Both maps are linear.

`extend_restrict` and `restrict_extend` prove that extension and restriction
are mutual inverses. They give the linear equivalence

`restrictEquiv hρ S hS : completion ρ hρ ≃ₗ[ℂ] completionOn ρ hρ S`.

`restrictEquiv_apply` gives its forward component formula;
`restrictEquiv_symm_apply` gives the inverse formula for every admissible
choice of `L`. The inverse is defined using a chosen index below each `K`;
the independence lemma proves that its value does not depend on that choice.
No local compactness or nonemptiness of the set of compact open subgroups
is assumed.

This proves the change-of-index construction for a supplied cofinal family.
VI.9.7 still requires the specific geometric cofinality theorem, compatible
Jacquet stable-image isomorphisms, and the identification of their limit
with the radical-fixed completion. Neither exact target of the task is
proved by this module.
