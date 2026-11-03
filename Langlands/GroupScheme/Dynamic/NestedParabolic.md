# Compatible nested dynamic parabolics

This module defines predicates for the nested decompositions used by Renard
VI.1.4 (printed p.136, PDF p.142) and the compatible semistandard setting of
V.3.10–V.3.11 (printed p.112, PDF p.118). It does not assert the structural
decomposition theorem.

`Dynamic.IsCompatibleNestedPair χ ψ` requires the all-test inclusions
`P(χ) ≤ P(ψ)` and `Z(χ) ≤ Z(ψ)`, together with a common maximal split torus
`i : T → G` and cocharacters `α, β` of `T` whose composites with `i` are
`χ, ψ`. Thus `M = Z(χ)` is contained in `L = Z(ψ)`, and both dynamic
decompositions use the same split-torus realization. The torus is maximal
split in `G`; `G` need not be split. No existence of such compatible data is
asserted. The constructor `isCompatibleNestedPair_of_torus` only bundles
these hypotheses, and the two projection lemmas extract the inclusions.

For subgroup functors `P, M, N, L, U`, the internal predicate
`SubgroupFunctor.NestedLeviDecomposition P M N L U` says that on every test
scheme `X`, writing `H = (L ∩ P)(X)` and `V = (L ∩ N)(X)`:

- `V` and `M(X)` are subgroups of `H`, `V` is normal in `H`, and they are
  complementary there, with the complement ordered as `V, M(X)`;
- `H = M(X) V`;
- `N(X) = V U(X)`;
- `P(X) = H U(X)`.

Each displayed product is the pointwise set product in the actual group
`Hom(X,G)`. The formula using `V` also expresses `(N ∩ L)(X) U(X)`, since
intersection is symmetric. The complement clause states uniqueness of the
semidirect factorization and matches the convention in
`StandardLeviIntersectionStatement`. The explicit first set product uses
the Levi factor on the left, as in Renard. No quotient of rational point
groups or generated subgroup replaces a displayed product.

`Dynamic.NestedParabolicDecomposition χ ψ` specializes that conclusion
predicate to `P(χ), Z(χ), U(χ), Z(ψ), U(ψ)`. The predicates apply to all
schemes over the base, including nonreduced tests. Evaluation at the identity
test `Spec k → Spec k` gives exactly the corresponding subgroups and set
products of rational points. The theorem
`NestedLeviDecomposition.identityTest_products` states these three product
equalities explicitly; its proof specializes the all-test predicate and
extracts its last three conjuncts.

## Sources and conventions

Renard's 9 July 2026 edition works over a nonarchimedean local field and
explicitly requires both nested parabolics to be semistandard in VI.1.4.
The separate 2010-edition corrections, PDF p.9, printed-p.156 entry, add
precisely that missing semistandard hypothesis. The present compatibility
predicate exposes the common maximal split torus and the inclusion of the
chosen Levis; it does not quantify over unrelated choices of Levi factors.

Borel–Tits, *Groupes réductifs* (1965), §4.4(c), printed pp.86–87
(PDF pp.33–34), describes parabolics contained in `P` as semidirect
products with `R_u(P)`. Section 4.7, printed pp.87–88 (PDF pp.34–35),
provides the rationality setting for intersections and Levi factors.
The ground field is arbitrary: §0.3, printed pp.57–58 (PDF pp.4–5),
also permits the interpretation as affine absolutely reduced group schemes.
Milne, *Algebraic Groups* (2017), §25.1 and §25.6–25.7, printed
pp.544–546 (PDF pp.560–562), supplies the modern cocharacter, Levi and
parabolic-intersection formulation over arbitrary fields.

The official Milne errata snapshot of 2 November 2026 was read. The
Chapter 25 correction makes the parabolic in §25.6(b) minimal; the present
predicate does not use that clause to identify an arbitrary Levi with the
centralizer of a maximal split torus. The errata also warns that the
relative-root-system proof in the classical sources is incomplete; this
module assumes no root-system classification assertion.

The common-cocharacter predicate and the all-test packaging are internal,
derived interfaces, not literal statements from these sources. Turning
compatible dynamic pairs in a connected reductive group into these
decompositions is a separate proposition target and proof obligation.

Source IDs:
`renard-2026-representations-groupes-reductifs-padiques`,
`renard-2010-corrections-complements`,
`borel-tits-1965-groupes-reductifs`,
`milne-2017-algebraic-groups`,
`milne-2017-algebraic-groups-errata-2026-11-02`.
