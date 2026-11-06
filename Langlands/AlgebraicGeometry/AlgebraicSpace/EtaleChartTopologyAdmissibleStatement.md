# The étale-chart topology is the topology of Conrad's Proposition 5.4

Author: Worker 105.

`EtaleChartTopologyAdmissibleStatement` states the claim made in the existence proof
of Proposition 5.4 of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.15. The claim is that the strongest topology
on `X(k)` making every chart map `U(k) → X(k)` continuous has all the properties of
the proposition. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
only states the claim and contains no proof.

Conrad writes on printed p.15: "To prove existence with the asserted properties,
consider the étale maps `f : U → X` from finite type `k`-schemes `U`. As we vary
through such maps, the images `f(U(k)) ⊆ X(k)` cover `X(k)`. We claim that the
strongest topology on `X(k)` making the maps `U(k) → X(k)` continuous (i.e., a subset
of `X(k)` is open when its preimage in each such `U(k)` is open) does the job." Just
before this, on the same page, he gives the uniqueness argument: "The uniqueness holds
due to the requirement on étale maps and the fact that for every `x ∈ X(k)` there
exists an étale map `U → X` from a scheme `U` admitting a point `u ∈ U(k)` such that
`u ↦ x` [Kn, II, Thm. 6.4]."

## Objects

`K : Type u` is a nontrivially normed field, and the algebraic spaces are the
Library's actual algebraic spaces `X : AlgebraicSpace (Spec (CommRingCat.of K))`.
The statement uses only existing Library definitions.

- `etaleChartTopology K X`, from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/EtaleChartTopology.lean`, is the
  topology on `RingPoints K X K` defined by Conrad's construction. A chart
  (`EtaleFiniteTypeChart K X`) is an actual scheme `U` of finite type over `Spec K`
  (structure morphism locally of finite type and quasi-compact) with a morphism
  `(schemeToSpace _).obj U ⟶ X` whose underlying transformation satisfies the
  Library's `IsEtale`. The topology is the supremum of the topologies coinduced from
  `schemePointTopology K U K` by the chart maps `U(K) → X(K)`, so a set is open
  exactly when its preimage in every chart is open
  (`etaleChartTopology_isOpen_iff`). As a family indexed by all spaces over
  `Spec K`, `etaleChartTopology K` has the type of the families `τ` in Proposition
  5.4.
- `IsHenselianValuedField K`, `IsQuasiSeparatedLocallyFiniteType K X`,
  `IsAdmissibleRationalPointTopology K τ` and
  `SeparatedRationalPointTopologyProperties K τ` are the predicates of the published
  Proposition 5.4 statement in
  `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianSpacePointTopologyStatement.lean`.
  Its Markdown lists the six admissibility clauses: functoriality, agreement with the
  scheme point topology on schemes, fibre products, and open immersions, closed
  immersions and étale morphisms going to open embeddings, closed embeddings and
  local homeomorphisms. It also lists the separated-space properties: Hausdorff,
  totally disconnected over ultrametric `K`, and locally compact over locally
  compact `K`. As there, all clauses concern only quasi-separated spaces locally of
  finite type over `Spec K`.

## The statement

`EtaleChartTopologyAdmissibleStatement` says: for every nontrivially normed field
`K : Type u` with `IsHenselianValuedField K`,

1. `IsAdmissibleRationalPointTopology K (etaleChartTopology K)` holds;
2. every family `τ'` with `IsAdmissibleRationalPointTopology K τ'` satisfies
   `τ' X = etaleChartTopology K X` for every space `X` with
   `IsQuasiSeparatedLocallyFiniteType K X`;
3. `SeparatedRationalPointTopologyProperties K (etaleChartTopology K)` holds.

## Relation to the source and to Proposition 5.4

Clause 1 is Conrad's claim that this topology "does the job", that is, has all
the properties of the first paragraph of Proposition 5.4. Clause 2 is his uniqueness
assertion, with the unique topology now named. Clause 3 is the second paragraph of
the proposition for this topology.

The statement is Proposition 5.4 with the existing topology made explicit.
Taking `τ := etaleChartTopology K` shows that it implies the published
`HenselianSpacePointTopologyStatement`. Conversely, that statement together with
clause 1 gives clauses 2 and 3. By uniqueness, every admissible family, in particular
the family of Proposition 5.4, agrees with `etaleChartTopology K` on the spaces in
question, and the separated-space properties only concern those spaces. The point of
the module is the identification. Later statements of Section 5 (base change of the
ground field in Proposition 5.11, integral points in Corollary 5.7) can then use the
concrete `etaleChartTopology` instead of an unnamed family.

Conrad's étale maps from schemes are the Library's charts. For a morphism from the
space of an actual scheme to an algebraic space, the Library's `IsEtale` means
representable with étale represented projections. Morphisms from schemes to
algebraic spaces are representable, because the diagonal of an algebraic space is
representable. For representable morphisms this agrees with étaleness in the Stacks
Project sense (`IsEtaleMorphism`, Properties of Algebraic Spaces, Definition 16.2,
Tag 03FR). The text after that definition says: "whenever `X → Y` is a
representable morphism of algebraic spaces, then this agrees with the notion defined
via Spaces, Definition 5.1" (registered source
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`). The charts are restricted
to finite type schemes as in Conrad's construction. This loses nothing for
uniqueness: Conrad's argument needs, for each point `x ∈ X(K)`, a chart through
`x`. The published `RationalPointEtaleLiftStatement` provides an étale map from an
affine scheme `U` with a rational point over `x`, and such a `U` is of finite type
over `K` when `X` is locally of finite type.

Also derived here: the name of the statement and the bundling of the three clauses.
The family `etaleChartTopology K` is defined on all algebraic spaces over `Spec K`,
but only its values on quasi-separated spaces locally of finite type are constrained.

## Not stated here

- The third paragraph of Proposition 5.4, on `k`-analytic manifold structures, is
  not part of this statement.
- Conrad's remark that the chart images cover `X(k)` is not stated separately. It
  follows from `RationalPointEtaleLiftStatement` for quasi-separated spaces locally
  of finite type.
- The steps of Conrad's existence proof are not stated separately. These are: chart
  maps are open (via Lemma 5.3 applied to `U ×_X U'`), the topology is functorial,
  it is compatible with fibre products, and open and closed immersions give open and
  closed embeddings.
