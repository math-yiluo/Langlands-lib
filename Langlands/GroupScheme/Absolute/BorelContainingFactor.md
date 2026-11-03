# Borel embeddings inside an intermediate closed subgroup

Worker 1368, with the factorization interface and proof plan supplied by Worker
1427.

This internal helper applies the published definition of `IsBorelSubgroup` to
actual factorizations. It reuses `IsBorelSubgroup.of_comp` from
[BorelPromotion](BorelPromotion.md). It uses no new assertion from the literature.

Let `i : P ⟶ G` be a closed subgroup over a field `k : Type u`. If
`f ≫ i : B ⟶ G` is Borel, then `f : B ⟶ P` is Borel. The source group,
its smoothness, connectedness and solvability are unchanged. Mathlib's
`IsClosedImmersion.of_comp_isClosedImmersion` proves that `f` is a closed
immersion. Every competing smooth connected solvable closed subgroup of `P`
composes with `i` to give such a subgroup of `G`. Applying maximality of
`f ≫ i` to that composite proves maximality of `f`.

`IsBorelSubgroup.of_closed_factor` expresses the same conclusion for separate
maps `j : B ⟶ G` and `f : B ⟶ P` satisfying the actual equation `f ≫ i = j`.
No connectedness, smoothness or affineness of the intermediate ambient group
`P` is needed by these helper lemmas. They do not prove connectedness of `P`.

When both embeddings `j : B ⟶ G` and `i : P ⟶ G` are Borel,
`IsBorelSubgroup.isoOfFactor hj hi f hf` constructs an actual isomorphism
`B ≅ P` from a factorization `hf : f ≫ i = j`. The maximality of `j`
applied to `i` proves that `f` is an isomorphism; the construction is `asIso f`.
The lemmas `isoOfFactor_hom` and `isoOfFactor_hom_comp` identify its
homomorphism with `f` and prove the original embedding equation. This
construction requires the Borel hypothesis on `i`, unlike the preceding
factor lemmas. It gives no isomorphism to a general subgroup containing a
Borel.
