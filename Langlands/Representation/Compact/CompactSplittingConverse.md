# Category splitting forces finite fixed-level strata

Author: Worker 88. This is the converse of Renard IV.1.7 Proposition and
proof, printed pp.95–96 / PDF pp.101–102. The original is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The module is derived proof support for the exact criterion, not a new premise.

`finite_compact_quotient_classes` is algebraic. Let a smooth complex object
`A` be finite over its actual group algebra, and suppose its total intrinsic
compact-isotypic part is top. The group need only carry a topology; all
stronger topological hypotheses are omitted from this helper. Its conclusion
is finiteness of the set of compact classes `c` admitting a nonzero morphism
`A → c.out.obj`, with representatives in the same carrier universe as `A`.
No admissibility or semisimplicity premise is used.

The subrepresentation/group-algebra-submodule order isomorphism identifies
its total-isotypic spanning equality with a supremum covering the top
submodule. Finite generation makes that top submodule a compact lattice
element. Its compactness selects finitely many isotypic classes already
spanning `A`. For every other class `c`, Schur separation puts each of these
parts in the `c`-annihilator. The whole object lies there, so every map to a
representative of `c` is zero. The class set of nonzero outgoing maps is
therefore contained in that finite set. This expresses the source's
finite-length conclusion directly through a finite isotypic cover.

`finite_strata_of_compactCategoryDecomposition` takes the assumed exact
A.IX category decomposition on a Hausdorff locally compact totally
disconnected sigma-compact group. It proves the required finite stratum
for every open subgroup `K`; compactness of `K` is not needed for this
implication. The group and carrier universes are independent.

The topological quotient `G/K` is discrete because `K` is open. It is a
continuous surjective image of the sigma-compact, hence Lindelof, group,
so is itself Lindelof and consequently countable. Countable types are small
in every carrier universe. The published
`Jacquet.smallFixedVectorGenerator.{u,v} K` therefore supplies the compact
permutation representation, equivalent to compact induction of the trivial
character, with its basis reindexed into exactly `Type v`. Its identity-coset
vector is `K`-fixed and generates the actual group-algebra module, as proved
in the imported constructor. This prevents a hidden relation between the
group and carrier universes.

Apply the assumed decomposition to this generator `E`. Its actual coproduct
cofan has compact component `A = Y true` and noncompact component `Y false`.
The published coproduct projection `r : E → A` retracts its inclusion, so
is surjective. Hence `A` remains finite over the group algebra. Its constituent
condition and `CompactPartExhaustion` give total-isotypic exhaustion. The
preceding finite-quotient-class helper thus applies to `A`.

For a compact class `c` in the `K`-fixed stratum, take a nonzero fixed vector
in its chosen representative. The published `smallFixedVectorLift` gives a
morphism from `E` to that representative; evaluating at the identity-coset
vector gives the chosen nonzero vector, so the morphism is nonzero. Compact
coefficients pass to every actual subquotient, placing this representative
in the decomposition's compact factor. The off-diagonal Hom condition kills
the map from `Y false`. If the map from `Y true` were also zero, the coproduct
universal property would make the original morphism zero. Its restriction
to `A` is consequently nonzero. Thus every class in the stratum belongs to
`A`'s finite quotient-class set, proving (KF).

The proof uses the source's compact-induction, projectivity and finite-type
route, with actual Library constructors for all category and vector-space
maps. There is no global coproduct-size assumption, carrier resizing
hypothesis left to the consumer, or replacement of irreducible subquotients
by a finite-length subset.
