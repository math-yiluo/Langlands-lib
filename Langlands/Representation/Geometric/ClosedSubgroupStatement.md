# Closed-subgroup Mackey-filtration targets

Worker 14 states the finite-orbit ordering prerequisite and the natural
closed-subgroup Mackey filtration. These are Lean proposition definitions.
No proof of either assertion is supplied or assumed.

## Exact assertions

`ClosedSubgroupOrbitOrdering` quantifies a group with a Hausdorff,
locally compact, nonarchimedean topology and sigma compactness, and two
closed subgroups `P` and `Q`. If the actual Mathlib double-coset quotient
`P \ G / Q` is finite, there is a finite list of representatives whose actual
orbits in `P \ G` are a disjoint cover and whose initial unions are open.
The length is existentially quantified, with an ordinary finite type `Fin n`;
there is no arbitrary finite-indexing predicate.

`ClosedSubgroupMackeyFiltration` has the same group and closed-subgroup
hypotheses. For every specified finite orbit ordering, it asserts that the
successive quotients of the actual natural support filtration are naturally
isomorphic to the concrete functors `orbitPiece`. The input category
consists of all smooth complex representations of `P` with arbitrary
carrier in the specified universe and all actual intertwining maps.
Each quotient is a genuine quotient representation. Each comparison is an
isomorphism of functors, not only an isomorphism for individual inputs.

The orbit containing `P w^-1` contributes
compact induction to `Q` from the subgroup
`{q : Q | w^-1 q w belongs to P}`, applied to the original representation
pulled back by `q -> w^-1 q w`. The comparison uses no unspecified
representation, no selected list of constituents, and no hypothetical
functorial action supplied by the caller.

The representation carrier and group universes are independent. Compact
induction has carrier universe `max uG uV`. Coefficients are exactly the
complex numbers in the theorem targets. No admissibility, finite dimension,
finite length, irreducibility, unitarity, or openness of `P` or `Q` is
required. In the second target finite orbits are supplied by the actual
ordered cover, rather than by an additional redundant finiteness premise.

`ClosedSubgroupMackeyTheorems` is the conjunction of these two assertions.
The statements retain the ordering prerequisite as its own named target,
so constructing an ordered cover is not silently assumed to follow from
finiteness.

## Original reference and specialization

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I*, Annales scientifiques de l'ENS (4) 10 (1977), 441-472:

- Section 1.1, printed page 442 (PDF page 3), defines an l-group by
  Hausdorffness and a compact-open subgroup basis.
- Sections 1.2 and 1.8, printed pages 443-445 (PDF pages 4-6), give the
  smooth complex category, the uniform right stabilizer, the compact support
  condition and right-translation action.
- Section 5.1, printed pages 459-460 (PDF pages 20-21), supplies closedness,
  countability at infinity, finiteness of the orbit set, and the ordering
  by open initial unions. It explicitly cites its reference [1], section 1.5,
  for the orbit-ordering assertion.
- Theorem 5.2 and section 5.3, printed pages 460-461 (PDF pages 21-22),
  identify the ordered support filtration and its natural graded pieces.

These original passages were read. The formulas and ordering condition on
printed page 460 were also checked visually. Literature ID:
`bernstein-zelevinsky-1977-induced-i`; retained original SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Set `U=V={1}`, `M=P`, `N=Q`, and both localization characters to one in
the source's theorem. Trivial groups satisfy the compact-subgroup-limit
condition. Both decomposability requirements become identities of actual
subgroups. Localization is restriction; both modular corrections are one.
The resulting graded functor is exactly `orbitPiece` above. The support
filtration in the definitions is the source's section 5.3 construction
under this specialization.

The source's l-group condition is expressed using Mathlib's
`NonarchimedeanGroup`, local compactness and `T2Space`. The already published
`Langlands.compactOpenSubgroupBasis` proves the required compact-open
subgroup basis from these hypotheses. `SigmaCompactSpace` expresses the
countability-at-infinity assumption as a countable compact covering.
There is no coefficient-space topology.

## Dependencies and proof obligations

The targets import the actual compact-induction construction by its Library
Lean name, the compact-open basis theorem, and the published concrete
closed-subgroup and natural-filtration definitions. The closed-subgroup pair
was integrated at Library commit `fc2adf231e015f979345e06d0d80283856c43c7f`;
its restriction functor is Mathlib `Rep.resFunctor`. No definitions are
supplied as assumed theorem fields.

The ordering assertion and the natural graded-piece isomorphisms are
unproved here. A future proof of the former must inspect the original
argument cited as [1], section 1.5, or provide a different complete proof;
this pair cites the assertion as it is stated in BZ77. No inaccessible or
unread proof is claimed as verified.

The full parabolic geometric lemma 2.12, its normalized Jacquet and modular
compatibilities, and the cuspidal-support results of sections 2.5, 2.8-2.9
and 2.13 remain separate obligations. This special case does not complete
the geometric-lemma subfamily or the parent classification task.
