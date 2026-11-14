# Maximal bounded vertex one-stabilizers over the unramified field

Worker 283, with Worker 347. The theorem
`MaximalUnramified.vertexOneStabilizerMaximalBounded` proves the exact Library
proposition `MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement`
at arbitrary universe `u`. It has no additional hypotheses.

For every nonarchimedean local field `F`, put
`K = inertiaFixedField F`. For every affine group scheme `G` over this actual
field, supplied `C : BuildingData F G`, and actual vertex `y` of the original
quotient `C.ReducedBuilding`, the subgroup `C.oneStabilizer y` is maximal among
the algebraically bounded subgroups of `rationalPoints G`. This includes
algebraic boundedness of the one-stabilizer itself. All bounds use every global
regular function on the original affine group and exactly
`ValuativeRel.ofValuation (fixedFieldValued F).v`.

The proof installs that prescribed valuative relation and the published
compatibility of `valuation F` with it. It then supplies the two inputs to
`C.maximal_oneStabilizer_vertex_of_isAlgebraicallyBounded`:

1. `MaximalUnramified.commonApartments` proves that the original quotient
   has common translated apartments for every supplied `C`.
2. The published reduction
   `oneStabilizerBounded_of_centralizer_of_zeroRootFiltration`, applied to
   the proved theorems `centralizerNormOneBounded` and
   `zeroRootFiltrationBounded`, proves algebraic boundedness of
   `C.oneStabilizer y`.

The maximality helper uses a direct finite-orbit argument. For an algebraically
bounded overgroup of a vertex one-stabilizer, the normalizer part has a finite
apartment orbit. Its centroid is fixed by that normalizer part. Actual affine
reflections through the vertex lift into the vertex sharp fixer, which lies in
the overgroup. They force the centroid to lie on every root hyperplane through
the vertex; local finiteness and the singleton-facet definition identify it with
the vertex. Common-apartment factorization then makes the entire overgroup fix
that vertex. Algebraic boundedness places it in the character-valuation kernel,
so it is contained in the one-stabilizer. Bounded conjugation transfers the
argument to every actual vertex. Together with the one-stabilizer's own bound,
this proves `Maximal`.

This is an internal assembly of Library theorems proving the maximal-bounded
part of Kaletha–Prasad Theorem 4.2.15(1) specified by the target pair. The
implemented maximality proof uses the finite-orbit argument above. It assumes
no complete metric on the building and no completeness or local compactness of
`K`. It adds neither an integral model nor a descent assumption on `G`, and
makes no additional assertion of openness.

The accompanying change to `UnramifiedTorusNormOneBoundedness.lean` gives
explicit names to its three local instances on `F`. Their types and values
are unchanged. This prevents their generated declaration names from colliding
with those in `UnramifiedOmegaGaloisStable` when the centralizer and
vertex-overgroup proof chains are imported together. The torus module's paired
mathematical explanation is unchanged. The target pair and every pair it
imports are unchanged.
