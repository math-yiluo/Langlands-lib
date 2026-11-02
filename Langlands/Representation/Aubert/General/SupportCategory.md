# Cuspidality, cuspidal series and the support categories `Alg({I})`

Implementation and documentation: Worker 379 (task
`0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`, the complex-and-targets unit of the
general Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`).

This module defines the predicates that pick out the representations to which
Aubert's corrected Theorem 3.6 applies:

* cuspidality, for `G` and for every standard Levi subgroup;
* the cuspidal series `𝔈(I)` of Aubert's Notation 1.6;
* the full smooth support category `Alg({I})` of the 1996 erratum.

Besides the definitions it proves only intrinsic laws that follow from the
definitions and from published generic facts about subquotients: closure of
`Alg({I})` under subquotients, isomorphisms and extensions, membership of the
induced representations that occur in its definition, and, when the identity
element represents the association of `I` with itself, membership of the
cuspidal induction `i^G_{L_I}(σ)` and of the cuspidal series `𝔈(I)`. The
support theory proper (existence and uniqueness of cuspidal support up to
association, detection of zero by Jacquet modules, stability of `Alg({I})`
under `i ∘ r`) is not asserted here.

## Generic layer

The module works over the generic standard families of Worker 23's adapter
modules `Langlands.Representation.Aubert.General.Parabolic` and
`Langlands.Representation.Aubert.General.AlternatingOperator` (namespace
`Langlands.Aubert.General`):

* `G : Type uG` is a group with `[TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]`;
* `ι` is the type of simple roots, and `S` is `Finset.univ : Finset ι`;
* `P M U : Finset ι → Subgroup G` are the standard parabolic subgroups `P_I`,
  their standard Levi subgroups `L_I = M I` and their unipotent radicals `U I`;
* `h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)` records
  `P_I = L_I ⋉ U_I`, and `hU : ∀ I, IsClosed (U I : Set G)`.

No reductive structure is constructed or assumed. For the rational points of a
connected reductive group these families, the decompositions and the closedness
facts are supposed to come from the owners of the shared Renard Chapter V
objects. Any family of the stated shape can be substituted, and the predicates
then have the stated meaning for that family only.

The functors are Worker 23's: `jacquetFunctor (h I) (hU I)` is the normalized
Jacquet functor `r^G_{L_I}`, `normalizedInductionFunctor (h I) (hU I)` is the
normalized parabolic induction `i^G_{L_I}`, and `conjugationFunctor n hn` is the
transport `σ ↦ (x ↦ σ(n⁻¹ x n))` from representations of `M I` to those of
`M J` when `hn` says that `M J = n (M I) n⁻¹`. Aubert (p. 2180) uses the
Bernstein–Zelevinsky normalized functors of [BZ, 2.3]. As `Parabolic.md`
explains, the Jacquet functor is BZ's `r_{U,1}` for every decomposition, while
the induction functor is BZ's normalized induction only when `U I` is
unimodular (`IsUnimodularModulus`). That holds for unipotent radicals, which are
limits of compact subgroups (`isUnimodularModulus_of_isLimitOfCompactSubgroups`),
so it holds in the intended application. For other families the predicates
below use the generic induction of the adapter, which has no counterpart in the
sources.

## Cuspidality

`IsCuspidalFor P M U h hU A`, for any family `κ → Subgroup H` of semidirect
decompositions `P k = M k ⋉ U k` of a group `H` with every `U k` closed, holds
when the normalized Jacquet module of `A` along every member of the family is
zero, that is, its carrier is a subsingleton.

`IsCuspidal P M U h hU A` is the instance for `G` and the proper standard
parabolics, indexed by the subtype `{I : Finset ι // I ≠ Finset.univ}`. It
states `r^G_{L_I}(A) = 0` for every `I ⊊ S`. This is the definition recalled
by Aubert on p. 2181: "π ∈ Irr(G) est dite cuspidale si r^G_{L_I}(π) = 0 pour
tout I ⊊ S (cf. [BZ, §2.4])". Aubert states it for irreducible π. The predicate
makes sense for every smooth representation, and this module applies it only
together with irreducibility.

`IsLeviCuspidal P M U hU J hM hJ σ` is cuspidality for the standard Levi
`L_J = M J`, for a smooth representation `σ` of `M J`. The standard parabolics
of `L_J` are indexed by the subsets of `J` (`I : Finset J`, read in `ι` through
`leviIndex J I`). For such `I` the parabolic of `M J` is
`(P I) ∩ M J = (M I) ⋉ (U I ∩ M J)`, as subgroups of `M J`
(`Subgroup.subgroupOf`). The hypothesis `hJ` supplies these decompositions; it
is the same hypothesis as for Worker 23's `leviAlternatingOperator`, and `hM`
says that `M J` is closed, so that `M J` is locally compact. The predicate
states `r^{L_J}_{L_I}(σ) = 0` for every `I ⊊ J`. The Jacquet functor for `I` is
the one of the adapter modules, taken for the subgroup `U I ∩ M J` of `M J`,
which is closed by `hU`.

## The cuspidal series 𝔈(I)

`IsInCuspidalSeries P M U h hU I hM hI π` is Aubert's Notation 1.6, p. 2181:
"`𝔈(I)` [est] le sous-ensemble de Irr(G) formé des représentations de G qui
sont sous-quotients de représentations induites `i^G_{L_I}(σ)`, avec `L_I`
sous-groupe de Levi standard de G et σ représentation irréductible cuspidale de
`L_I`". In Lean, `π` is irreducible (`SmoothRep.IsIrreducible`, which includes
`π ≠ 0`), and there is a smooth representation `σ` of `M I` that is irreducible,
satisfies `IsLeviCuspidal` and has `π` as a subquotient of
`(normalizedInductionFunctor (h I) (hU I)).obj σ`. Subquotients are
`SmoothRep.IsSubquotient`: an actual subrepresentation of a quotient, up to
isomorphism. Membership is a predicate on representations, not on isomorphism
classes; it is invariant under isomorphism because `IsSubquotient` is.

## The support category Alg({I})

`IsInSupportCategory P M U h hU IsAssociate I hM hI E` is the definition of the
erratum, p. 4687: "`Alg({I})` [est] la sous-catégorie abélienne de la catégorie
des représentations lisses de G constituée par les représentations de G dont tout
sous-quotient irréductible est sous-quotient d'une représentation induite
`i^G_{L_{v(I)}}(Ad(v)(σ))`, où σ est une représentation irréductible cuspidale du
sous-groupe de Levi standard `L_I` de G et `v ∈ W` est tel que `v(I) ⊂ S ∩ Φ⁺`
(autrement dit, `L_I` et `L_{v(I)} = v L_I v⁻¹` sont des sous-groupes de Levi
standard associés de G, et `Alg({I})` ne dépend que [de] la classe d'association
de `L_I`)". As `S ⊆ Φ⁺`, the condition is `v(I) ⊆ S`. In
Lean: for every irreducible subquotient `π` of `E` there are an index set
`J : Finset ι`, an element `n : G`, a proof `hn` that `M J = n (M I) n⁻¹`, and
an irreducible cuspidal `σ` of `M I`, such that `IsAssociate I J n` holds and
`π` is a subquotient of
`(normalizedInductionFunctor (h J) (hU J)).obj ((conjugationFunctor n hn).obj σ)`,
that is of `i^G_{L_J}(Ad(n)σ)`.

The Weyl element `v` of the erratum enters through the relation
`IsAssociate : Finset ι → Finset ι → G → Prop`, which is a parameter. Its
intended instantiation is: `n` represents an element `v` of the relative Weyl
group `W` with `v(I) = J ⊆ S`. Aubert writes `W := N_G(T_0)/T_0` (p. 2180); for
nonsplit groups the relative Weyl group is `N_G(T_0)/Z_G(T_0)`. The relation
`hn` is the Levi-level consequence `L_{v(I)} = v L_I v⁻¹` that the erratum
records in its parenthesis. The relation itself, and its agreement with the root
datum, belong to the structural framework: they are requirement A02 (actual simple
roots, relative Weyl group and Levi transport) of the structural ledger of the
general Aubert program.
With a weaker relation the predicate is weaker, and with a stronger one it is
stronger, so the faithfulness of `Alg({I})` for an actual reductive group rests on
that instantiation.

A second faithful instantiation is the trivial relation
`IsAssociate := fun _ _ _ => True`. Then the condition reads: `π` is a
subquotient of `i^G_{L_J}(Ad(n)σ)` for some standard Levi `L_J` and some `n ∈ G`
with `L_J = n L_I n⁻¹`. Every witness of the erratum's definition is such a
witness. Conversely, standard Levi subgroups that are conjugate in `G` are
associated by an element `v ∈ W` with `v(I) = J`, and `n = v m` with `m` in the
normalizer of `L_I`; since `σ` ranges over all irreducible cuspidal
representations of `L_I`, and `Ad(m)σ` is again one of them, the two classes of
induced representations coincide. So this instantiation is equivalent to the
erratum's definition given that structural fact (again requirement A02). It needs
no Weyl-group data, only the standard families. For the rational points of a
connected reductive group, the published families
`Langlands.Aubert.General.RationalPointFamily.parabolic`, `levi` and `unipotent`
are the intended `P`, `M` and `U`.

The membership condition `hn` is required for every witness `n`, so
`conjugationFunctor n hn` lands in representations of `M J`. The representation
`σ` lies in the carrier universe `max uG uV` of `E`, and induction keeps that
universe.

Three features of the erratum's definition are kept:

* `E` is an arbitrary smooth representation. No finite length or admissibility
  is imposed, and the corrected Theorem 3.6 is stated for every such `E`.
* Only irreducible subquotients are constrained. The zero representation and
  every representation without irreducible subquotients belong to the category.
  This is the literal reading of "dont tout sous-quotient irréductible", and the
  separate statement targets record the facts (for instance detection of zero by
  Jacquet modules) that make the category behave as in the erratum.
* The witnesses `J`, `n` and `σ` may depend on the subquotient `π`.

The erratum adds that `Alg({I})` is an abelian subcategory and depends only on
the association class of `L_I`. These are properties, not part of the
definition. The closure laws below give the subquotient and extension part of
the first property. The second is not asserted here.

## Proved laws

Fix the data of `IsInSupportCategory`, with `IsAssociate`, `I`, `hM` and `hI`
implicit.

* `IsInSupportCategory.of_isSubquotient`: if `E ∈ Alg({I})` and `F` is a
  subquotient of `E` (`SmoothRep.IsSubquotient F E`), then `F ∈ Alg({I})`. An
  irreducible subquotient of `F` is an irreducible subquotient of `E` by the
  published transitivity of subquotients, `smoothSubquotientTransitivity`.
* `IsInSupportCategory.of_iso`: if `E ∈ Alg({I})` and `F ≅ E`, then
  `F ∈ Alg({I})`, by `SmoothRep.IsSubquotient.of_iso_right`.
* `IsInSupportCategory.of_subrepresentation_quotient`: if `S` is an invariant
  subspace of `E` and both the subrepresentation `S` and the quotient `E/S`
  (`SmoothRep.subrepresentation E S`, `SmoothRep.quotient E S`) lie in
  `Alg({I})`, then so does `E`. The proof uses the published
  `SmoothRep.irreducibleSubquotient_dichotomy`: an irreducible subquotient of
  `E` is a subquotient of `S` or of `E/S`.
* `isInSupportCategory_inducedConjugate`: for `J`, `n`, `hn` with
  `IsAssociate I J n` and an irreducible `σ` of `M I` with `IsLeviCuspidal`,
  `(normalizedInductionFunctor (h J) (hU J)).obj ((conjugationFunctor n hn).obj σ)`
  lies in `Alg({I})`; the witnesses are the given data, for every irreducible
  subquotient.
* `conjugationFunctorOneIso`: for a subgroup `L` and the trivial membership
  condition for the element `1`, the conjugation transport
  `(conjugationFunctor 1 hn).obj σ` is isomorphic to `σ`, through the identity
  linear map. This is a generic lemma about Worker 23's transport and holds for
  any topological group.
* `isInSupportCategory_cuspidalInduction`: if `hrefl : IsAssociate I I 1`, then
  for every irreducible cuspidal `σ` of `M I` the normalized induction
  `(normalizedInductionFunctor (h I) (hU I)).obj σ`, that is `i^G_{L_I}(σ)`,
  lies in `Alg({I})`. It is the case `J = I`, `n = 1` of the previous law,
  transported along the image under induction of `conjugationFunctorOneIso`.
* `IsInCuspidalSeries.isInSupportCategory`: under the same hypothesis `hrefl`,
  every `π ∈ 𝔈(I)` lies in `Alg({I})`, as a subquotient of some `i^G_{L_I}(σ)`.

The hypothesis `hrefl` holds for the intended instantiation of `IsAssociate`
(the identity of `W` maps `I` to `I`). It is a hypothesis, not proved here,
because `IsAssociate` is a parameter.

## Declarations

* `IsCuspidalFor` — Jacquet modules along a whole family vanish.
* `IsCuspidal` — cuspidality for `G` (Aubert p. 2181).
* `IsLeviCuspidal` — cuspidality for the standard Levi `M J`.
* `IsInCuspidalSeries` — `π ∈ 𝔈(I)` (Notation 1.6, p. 2181).
* `IsInSupportCategory` — `E ∈ Alg({I})` (erratum p. 4687).
* `IsInSupportCategory.of_isSubquotient`, `IsInSupportCategory.of_iso`,
  `IsInSupportCategory.of_subrepresentation_quotient` — closure laws.
* `isInSupportCategory_inducedConjugate`,
  `isInSupportCategory_cuspidalInduction`,
  `IsInCuspidalSeries.isInSupportCategory` — membership laws.
* `conjugationFunctorOneIso` — conjugation by `1` is isomorphic to the identity.

The five predicates are `Prop`-valued definitions. No declaration uses axioms
beyond Lean's standard ones.

## Sources

* A.-M. Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
  représentations lisses de longueur finie d'un groupe réductif p-adique*,
  Trans. AMS 347 (1995), printed p. 2180 (W, `L_I`, the functors) and p. 2181
  (cuspidality, Notation 1.6).
* A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), printed p. 4687 (definition
  of `Alg({I})`).
* I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ÉNS 10 (1977), §2.3 and §2.4 (the functors and
  cuspidality, as cited by Aubert).
