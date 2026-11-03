# Trivial contracting subgroups and full centralizers

This module gives the formal limit-decomposition and unipotent-radical
reductions used in the full-parabolic centrality criterion. All subgroup
equalities are equalities of functors on every scheme test.

For a group scheme `G` over any scheme `S`, a cocharacter `χ`, and a
separated structure morphism of `G`,
`Dynamic.centralizer_eq_parabolic_of_unipotent_eq_bot` proves

```text
Dynamic.unipotent χ = ⊥ →
  Dynamic.centralizer χ = Dynamic.parabolic χ.
```

For a point `g` of the parabolic on an arbitrary test, the published limit
homomorphism provides `l = limit χ g` in the centralizer and places
`g * l⁻¹` in the contracting subgroup. Triviality of that subgroup gives
`g = l`. The reverse inclusion is the published centralizer-to-parabolic
inclusion. This argument uses the actual limit and retains nonreduced tests.

`Dynamic.centralizerParabolicIsoOfUnipotentEqBot` constructs the resulting
canonical group-scheme isomorphism between any representatives
`iZ : Z ⟶ G` and `iP : P ⟶ G` of these subgroup functors. The theorem with
suffix `_hom_comp` proves that its forward map followed by `iP` equals
`iZ`. This uses the published uniqueness isomorphism for representatives
of the same subgroup functor; no choice of coordinates or rational-point
identification is used.

Over a field, assume that `G` is smooth and affine and has trivial
ground-field unipotent radical in the sense of
`HasTrivialUnipotentRadical G`. Let `j : H ⟶ G` be a closed homomorphism
representing the actual contracting subgroup and assume `IsUnipotent H`.
Then `Dynamic.unipotent_eq_bot_of_parabolic_eq_top` proves that a full
parabolic forces the contracting subgroup to be trivial. Normality follows
from the published normalization by the parabolic and the full-parabolic
hypothesis. Smoothness of `H` follows from `dynamicSmooth`; connectedness
follows from
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`. Applying
the ground-field radical predicate gives triviality of the range of `j`,
which is the contracting subgroup by representability.

Combining the reductions,
`Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent` proves the
full-parabolic/full-centralizer equivalence with exactly these hypotheses.
The reverse direction uses the published
`Dynamic.parabolic_eq_top_of_centralizer`.

## Provenance and boundary

These are internal deductions from the published actual subgroup functors,
limit decomposition, dynamic smoothness and connectedness, and
ground-field radical predicate. No new external assertion is used.
Connectedness of `G` is unnecessary for these reductions. The group need
not be geometrically reductive.

Unipotence of `H` is an explicit hypothesis and is not proved here. In
particular this module does not prove
`PseudoReductiveCentralCocharacterStatement` or intrinsic relative-root
reflection existence.
