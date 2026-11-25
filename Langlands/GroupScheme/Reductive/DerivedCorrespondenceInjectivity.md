# Injectivity in the derived-group correspondence

This internal result specializes the effective-epimorphism descent criterion in
[`SubgroupFunctor.FpqcProductReconstruction`](../SubgroupFunctor/FpqcProductReconstruction.md)
to the intersection maps in the published
[`DerivedTorusParabolicCorrespondenceStatement`](DerivedTorusParabolicCorrespondenceStatement.md).
It does not prove the existence of the required isogenies or the full correspondence.
Its provenance is the categorical consequence of those factorization clauses.

For arbitrary group schemes over an arbitrary scheme, let `d : D ⟶ G` and
`z : Z ⟶ G`, with `z` central. Suppose `i : P ⟶ G` and `i' : P' ⟶ G`
are monomorphisms of schemes over the base. Suppose multiplication by `Z`
on each intersection with `D` factors through an isogeny onto `P` or `P'`.
Then equality of the intersection ranges in `D` implies equality of the
ranges of `i` and `i'` in `G`.

The proof first postcomposes equality of the intersection projection ranges
with `d`. Each isogeny is finite, flat and surjective, so its underlying
scheme map is an effective epimorphism. The generic reconstruction theorem
then gives equality of the ambient subgroup ranges.

`DerivedCorrespondence.IsMaxTorus` is exactly the local conjunction in the
published target: the source is a relative torus, the embedding is closed,
and it is fibrewise maximal.
`maximal_torus_injective_of_isogenies` obtains monomorphisms from closed
immersions and applies the general result.
`parabolic_injective_of_isogenies` uses the monomorphisms in the relative
parabolic predicate and the finite-flat-surjective part of the supplied
central isogenies.

`GeometricClauses d z hz` is a `Prop`-valued definition collecting precisely
clauses 1, 2, 4 and 5 of the published target at fixed `d`, `z` and `hz`.
These clauses assert the intersection and product constructions in each
direction for tori and parabolics, with every isogeny and range equality
retained. This definition asserts no proof of those geometric inputs.

`correspondence_of_geometric_clauses` proves the unchanged published
`ReductiveDerivedTorusParabolicCorrespondenceStatement` conditionally on
these four clauses for every datum satisfying exactly the target's
hypotheses. It unpacks the four clauses, keeps them verbatim, and inserts
the two injectivity lemmas above. Reductivity of `G`, the closed normal
semisimple presentation `d` with torus fppf quotient, and maximality of the
closed central torus `z` are all retained in this premise. The theorem is
a reduction of the remaining proof obligation, not an unconditional proof
of the correspondence.

All assertions hold in every universe. The general injectivity lemma needs
no reductivity, normality, semisimplicity, smoothness or finiteness condition
on the base. It never equates the pointwise range of an isogeny with its
whole target; the proof descends containment in a monic represented subgroup.
