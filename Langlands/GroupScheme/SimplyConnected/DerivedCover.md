# Simply connected covers of actual derived subgroups

For an arbitrary field `k : Type u`, `IsSimplyConnectedDerivedCover d π`
is a proposition about supplied actual group-scheme homomorphisms
`π : C → D` and `d : D → G`. It requires `G` to be connected reductive,
`d` to exhibit the full scheme-theoretic derived subgroup using the
published `IsDerivedSubgroup`, and `π` to satisfy the published
`IsSimplyConnectedCover` interface. Thus the covering map is finite fppf
and surjective onto `D`. The ambient map used by consumers is `π ≫ d`.

This is derived packaging of two existing interfaces. Its mathematical
conventions come from Milne, *Algebraic Groups* (2017), Proposition 19.15,
printed p.401 (PDF p.417), and CGP, *Pseudo-reductive groups*, second edition
(2015), the definition preceding Corollary A.4.11 and that corollary,
printed pp.500–501 (PDF pp.526–527). Those passages concern simply connected
central covers of semisimple groups. The present interface applies such a
cover to an actual derived subgroup of a reductive group; semisimplicity
of the supplied `D` is included in `IsSimplyConnectedCover π`. It does
not prove semisimplicity or representability of every reductive derived
subgroup. The full registered Milne errata of 2026-11-02 was read and
does not change Proposition 19.15; no retained project CGP errata was found.

The implemented lemmas concern these supplied maps. A point in the range
of `π ≫ d` factors through `d`, so it belongs to `derivedSubgroup G`.
The closed derived-subgroup inclusion is a monomorphism. Cancelling it
shows, on every test scheme over the field, that a point is killed by
`π ≫ d` exactly when it is killed by `π`. The existing natural
`kernelPointsEquiv` identifies these conditions with membership in the
ranges of the actual kernel inclusions, yielding `kernel_range_eq`.
Centrality of the cover kernel consequently gives centrality of the
ambient-composite kernel.

Both actual kernels represent that same subgroup functor of `C`.
`kernelIso` applies the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` to construct an
actual group-scheme isomorphism between them. `kernelIso_hom_comp` says
that it preserves their inclusions into `C`. The point formula
`kernelIso_hom_points` gives this comparison on every test scheme, and
`kernelIso_hom_points_naturality` states its compatibility with restriction;
the latter is categorical associativity for this actual homomorphism.
No reduced kernel, smoothness of a kernel, or rational-point quotient is used.

The predicate chooses no derived group or covering group and proves no
existence or field-base-change theorem. In particular, it imposes no
surjectivity on `π ≫ d : C → G`. A connected reductive group can have a
central torus, while its simply connected cover here maps onto its
semisimple derived subgroup. Existence and structural comparisons remain
separate statement and proof obligations.
