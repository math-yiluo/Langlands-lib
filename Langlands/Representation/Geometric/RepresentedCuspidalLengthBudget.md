# Length budgets from supplied represented geometric filtrations

This internal consequence combines the actual proper-source vanishing, the
full-intersection irreducibility proof, the evaluated-gluing length formula,
and the exact detecting-Jacquet-family length criterion. It supplies no new
external mathematical input.

`IsomorphicLeviCuspidalLengthStatement` concerns a supplied finite list of
actual represented intersection data. The inducing representation is
irreducible and its proper normalized represented Jacquet modules all have
zero carrier. The outer source and target Levis are isomorphic. A supplied
actual geometric gluing then has composition length equal to the number of
original indices with full source intersection parabolic.

`isomorphicLeviCuspidalLength` proves this proposition. Proper-source pieces
vanish by `pieceFunctor_subsingleton_of_proper`. For each full-source piece,
`pieceFunctor_isIrreducible_of_isIso_source_of_iso` uses the supplied
outer-Levi isomorphism to make its target intersection full and proves
irreducibility of the actual three-functor piece. Applying
`representedJacquetInduction_repLength_eq_card_fullSource` now gives the
equality without any additional survivor-irreducibility premise. Every
original index remains counted, including isomorphic repeated pieces.

For a finite family of actual target parabolics, the same equality gives
natural-number Jacquet image bounds. The theorem
`hasRepresentedJacquetLengthWitness_of_geometricBudget` takes such a family,
outer-Levi isomorphisms, actual intersection data and gluings for its members,
a bound for the sum of the full-source index counts, and detection of every
irreducible actual subquotient of the induction. It constructs the existing
`HasRepresentedJacquetLengthWitness` with those exact cardinalities as its
budgets. Over a nonarchimedean local field, compact-limit radical point images
follow from the proved
`isLimitOfCompactSubgroups_pointImage_radical`; they are not additional
premises. The image-length bounds follow from the preceding equality.

Finally `induced_repLength_le_of_geometricBudget` applies the actual
detecting-family length criterion to this constructed witness. The proof
does not assume finite length of the induced representation.

The field and coefficient-carrier universes are independent. All functors
are the actual normalized represented induction and Jacquet functors, with
their canonical rational-point topologies; induced carriers have universe
`max u v`. The single-target statement only requires a Hausdorff topological
field and locally compact nonarchimedean ambient rational points. The
family-witness construction additionally uses the nonarchimedean local-field
hypothesis to prove radical compactness.

Intersection data, geometric gluings, a suitable finite family, the total
index count and subquotient detection remain explicit inputs. This module
does not construct a standard-Levi family, prove a Weyl-group count, derive
the unconditional maximal-Levi length bound, or prove the host
unitarizable-constituent theorem.
