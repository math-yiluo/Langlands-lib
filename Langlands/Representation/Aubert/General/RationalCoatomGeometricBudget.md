# Actual coatom Jacquet lengths from geometric filtrations

Author: Worker 153.

This unit is an internal deduction from published actual rational geometric-term,
root-association and representation-length constructions. It proves the coatom
Jacquet-length budget **from supplied actual finite geometric filtrations**. It
does not construct those filtrations or prove the unconditional
`RationalMaximalCuspidalJacquetBudgetStatement`.

## Count all surviving occurrences

`Langlands.Aubert.General.coatomFullSourceIndices` defines the finite sigma of
all original full-source grade occurrences. An index retains both its target
coatom label and its index in that target's finite list. This is the concrete
finite set used in the counting proof below; no occurrence is identified with
another one by this definition.

`Langlands.Aubert.General.coatomFullSourceIndicatorBudget` applies to any finite
Coxeter system, with independent simple-label and Weyl-group universes. For each
literal coatom label `a`, take a finite list `w a` of minimal representatives for
`W_(univ.erase a) \ W / W_(univ.erase b)`. Require that each list is injective.
The sum in `ℕ∞` of the indicators of full source intersection, over all labels
and all original list entries, is at most two.

The proof forms the finite sigma of all full-source entries. It maps `(a,q)` to
`(univ.erase a,w a q)`. The target coatom determines `a`, by `Finset.erase_inj`,
and injectivity of `w a` determines `q`. Equal coatom cardinalities, minimality
and fullness put every image in the original `fullIntersectionPairs` finset.
`card_fullIntersectionPairs_coatom_le_two` bounds that finset by two.
`Finset.card_sigma`, `Finset.sum_boole` and the natural-number cast compute the
sum of indicators as the cardinality of the sigma. Thus the count retains every
original grade occurrence. It requires no surjectivity onto all minimal classes,
no choice of two preferred terms, and no association-case split.

## Length of an actual geometric term

The rational results use actual connected reductive rational points with
`pointTopology`, an actual maximal split torus and generic cocharacter, closed
standard Levi and radical subgroups, and the displayed locally compact
nonarchimedean topology. They retain an actual point Coxeter system, the actual
point-normalizer and point-centralizer comparisons, and its root-length and
positive-simple-reflection comparisons. The field and representation universes
`u,v` remain independent; the carrier universe is `max (u + 1) v`.

For a minimum representative with equally large source and target simple-root
subsets, `pointGeometricTerm_isIrreducible_of_full_source_of_card` proves that a
full source intersection makes the actual term irreducible on irreducible input.
`rootImage_eq_of_full_intersection`, with the proved intrinsic
`minimalityLengthCriterion_proof`, gives equality of the actual root images.
Together with the same normalizer lift this gives `rootAssociation`.
`pointGeometricTermRootAssociationIso` identifies the term with pullback of the
inducing object along `rootAssociationLeviConjugationEquiv`.
`smooth_isIrreducible_of_iso_pullback` transports irreducibility. The
standard-cocharacter hypothesis supplies the actual Levi conjugation used by
these published comparisons. There is no separate target-fullness assumption.

`pointGeometricTerm_repLength` computes the composition length in `ℕ∞`. The full
source case has length one by this irreducibility result and
`repLength_eq_one_iff`. In the proper-source case,
`pointCuspidalGeometricTermVanishing_of_rootComparisons` gives a subsingleton
carrier, and `repLength_eq_zero_iff` gives length zero. Its original
`IsCorollaryLeviCuspidal` predicate and literal inside-Levi decompositions from
`isSemidirectDecomposition_in_levi` are retained. This uses the standard-Levi
intersection hypothesis. No finite-length, admissibility or exactness premise
is supplied.

## Add lengths along actual filtrations

`pointCoatomJacquetBudget_of_geometricFiltrations` takes a maximal standard
source `J`, an irreducible inside-Levi cuspidal smooth object `σ`, and, for every
coatom label `a`, the following actual data:

- a finite `ObjectRepFiltration` of the original normalized Jacquet module of
  the original normalized induction, named by `pointInducedJacquetObject`;
- an injective list of `(univ.erase a,J)`-minimal Weyl classes, with actual
  normalizer lifts representing those classes;
- actual source and target semidirect decompositions for each lift, and actual
  `Rep` isomorphisms from each graded quotient to the corresponding normalized
  `geometricTermFunctor` on `σ`.

It concludes that the sum of the actual Jacquet composition lengths over every
literal coatom label is at most two. Maximality writes `J = univ.erase b`.
`repLength_eq_sum_of_filtration` computes each original Jacquet length from all
its quotient grades; `repLength_congr` transfers each grade isomorphism.
`pointGeometricTerm_repLength` replaces the grade length by its full-source
indicator, since the source and target coatoms have equal cardinality.
`coatomFullSourceIndicatorBudget` bounds their total. This includes both the
self-associated and non-self-associated cases and the empty-root case, where
there is no maximal source. All lengths and sums are in `ℕ∞`, so the bound also
proves that the displayed actual Jacquet modules have finite composition
length. It does not infer that fact from a Grothendieck-class identity.

## Dependency boundary

The dependency route uses the intrinsic finite Coxeter count, actual root and
standard-Levi intersection/conjugation comparisons, vanishing of the source
Jacquet module from the given cuspidality condition, and additivity of actual
module length along a supplied finite filtration. The full-term isomorphism
reduces the full source and target induction/Jacquet terms to actual continuous
Levi-group pullback. Proper-source vanishing reduces to the restricted standard
Jacquet module killed by the original cuspidality predicate and to induction
of a subsingleton object.

No geometric-lemma existence theorem, adjointness theorem, cuspidal-support
theorem, character-independence theorem or Langlands classification theorem is
used in this route. The geometric filtration and its grade isomorphisms remain
explicit inputs, not proved consequences. Its actual-root comparisons likewise
remain visible in this helper; the closed target may discharge those by
`rationalWeylComparison`, `rootSpanPointCoxeterData` and
`positiveSimpleReflectionComparison_of_rootLength`. The unconditional target
still requires an independently proved actual filtration theorem with the
stated grade multiplicities. This unit neither replaces nor asserts a proof of
that missing geometric lemma.
