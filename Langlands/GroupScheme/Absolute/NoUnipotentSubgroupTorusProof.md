# Groups without nontrivial connected unipotent subgroups are tori

The theorem `Langlands.GroupScheme.noUnipotentSubgroupTorus.{u}` has exactly
`Langlands.GroupScheme.NoUnipotentSubgroupTorusStatement.{u}` as its type.
It retains every universe, algebraically closed field, and smooth connected
affine group in the published statement, with no additional hypotheses.
The statement and all existing Library modules remain unchanged.

## Source and implemented proof

The target is the first sentence of James S. Milne, *Algebraic Groups*
(2017), Corollary 17.25, printed p.359 (PDF p.375), source ID
`milne-2017-algebraic-groups`. Its field and group conventions are recorded
in the [statement](NoUnipotentSubgroupTorusStatement.md). The complete
registered errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
contains no correction to this corollary.

Milne's proof uses a Borel pair and Proposition 17.23. The implemented proof
instead combines published dynamic-subgroup and maximal-torus results:

1. The hypothesis implies that the ground-field unipotent radical is
   trivial. Thus the group is pseudo-reductive, and over the algebraically
   closed field it is connected reductive.
2. For every cocharacter `χ`, take the actual closed affine representative
   of `Dynamic.unipotent χ`. Published theorems give its smoothness,
   connectedness, and representation-theoretic unipotence. The hypothesis
   therefore makes its range, and hence `Dynamic.unipotent χ`, trivial
   on every test scheme.
3. Choose a maximal torus `j : T ⟶ G`. It is split over the algebraically
   closed field, so it admits a generic integral cocharacter `ν`.
   `Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot` makes the opposite
   parabolic the whole group. The limit-decomposition equality
   `Dynamic.centralizer_eq_parabolic_of_unipotent_eq_bot` and invariance
   of the centralizer under negation show that the centralizer of `ν`
   is also the whole group.
4. `genericCentralizer` identifies that dynamic centralizer with the
   centralizer of `T`. `algClosedMaximalTorusCentralizer` identifies the
   latter with the all-test range of `j`. Thus `j` represents the full
   subgroup functor, yielding an actual isomorphism `T ≅ G`.
   Transporting the torus predicate along this isomorphism proves the target.

These combinations are internal deductions from the imported Library
theorems; they are not attributed to Milne as his printed proof.
The argument uses subgroup functors on every scheme test throughout.
