# Admissibility characterized by smooth biduality

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

The theorem `admissibleBidual` proves exactly `AdmissibleBidualStatement`, Renard III.1.7, both for the canonical evaluation map and for the existence of any representation equivalence with the double smooth contragredient. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, printed p.62 / PDF p.68; registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The source refers to the corresponding algebraic admissible-duality assertion in I.5.1. The implementation instead works directly on fixed-vector spaces, using the published compact-open smooth-dual restriction theorem and admissible smooth-bidual theorem.

First, `finiteDimensional_of_bidual_equiv` proves an internal linear-algebra observation: a complex vector space admitting any linear equivalence with its full algebraic double dual is finite dimensional. If its rank were infinite, Mathlib's `lift_rank_lt_rank_dual` would strictly increase rank twice. The resulting strict inequality contradicts rank equality under the supplied equivalence. This argument does not require the equivalence to be canonical evaluation.

Next, `isAdmissible_of_smooth_bidual_equiv` assumes a cofinal supply of compact open subgroups and a smooth representation equivalent to its double smooth contragredient. For a compact open `K`, restriction of this equivalence identifies the original `K`-fixed vectors with the double smooth contragredient's fixed vectors. Applying the compact-open restriction theorem twice identifies the latter with the full algebraic double dual of the original fixed space. The second identification uses the dual of the inverse of the first restriction equivalence. The internal rank observation makes this fixed space finite dimensional. The published cofinal admissibility criterion supplies finiteness for every open subgroup.

For the final theorem, the published Van Dantzig theorem supplies precisely the cofinal compact open subgroups from the stated topological hypotheses. Published admissible duality proves the forward bijectivity of canonical evaluation. A bijective canonical map supplies a representation equivalence; any such equivalence gives admissibility by the converse just proved. Thus both equivalences in the unchanged statement follow. The group and carrier universes remain independent and no hypothesis is added.
