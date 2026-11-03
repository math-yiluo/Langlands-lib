# An actual Borel containing a given admissible subgroup

`Langlands.GroupScheme.BorelExistence.BorelOverData j` records an actual
Borel embedding `i : B ⟶ G` and an actual factor `f : H ⟶ B` of the
given embedding `j : H ⟶ G`, with the equation `f ≫ i = j`.
`BorelExistence.borelOverData j hj` chooses these data when `hj` proves
that `j` is admissible and the ambient group is affine and locally of
finite type over a field. The universe and characteristic are arbitrary.

Admissibility is the published `BorelExistence.IsAdmissible` conjunction:
the embedding is closed and its source is smooth, connected, and solvable
in the published geometric-point sense. Borel means exactly the published
`IsBorelSubgroup`, with maximality among such subgroups defined over the
given field. No geometric maximality over a nonclosed field is asserted.
The ambient group need not be smooth or connected.

`BorelExistence.exists_minimal_height_admissible_over` adapts the published
absolute minimization to the family of admissible embeddings through which
the given `j` factors. This family is nonempty: it contains `j` itself,
using the identity factorization. Applying `Nat.find` to the natural-number
heights of its coordinate kernels gives a member of minimal height.
The published `BorelExistence.coordinateKernel_height_ne_top` converts
the resulting natural-number comparison into an extended-natural
comparison of heights.

The data constructor reuses the published
`BorelExistence.exists_isBorelSubgroup_containing` from `Absolute/BorelContaining`.
That theorem upgrades a minimal-height admissible overgroup to a Borel:
composition with any further inclusion preserves the factorization of `j`,
and `BorelExistence.isIso_of_coordinateKernel_height_le` proves maximality.
Classical choice retains the actual factorization; no canonical Borel is chosen.

`BorelOverData` remains a separate record from the existing `BorelContainingData`:
the equation projection is named `factorization`, and its chosen witness is not
asserted to coincide with `borelContainingData`. The additional exported result
here is the restricted minimum-height property above.

The original source is Milne, *Algebraic Groups* (2017), Definition 17.6 and
the following largest-dimension observation, printed pp.353–354 (one-based
PDF pp.369–370), and the containment step in the proof of Theorem 17.10,
printed p.355 (PDF p.371). Restricting to overgroups of the given subgroup
makes the maximality argument relative to it. The implemented proof uses
finite prime-kernel height instead of dimension, through the existing
`BorelExistenceCoordinates` results. This is derived internal content; its
more general ambient and field hypotheses follow from the implemented
coordinate argument. The complete registered official errata snapshot
dated 2 November 2026 has no correction to the cited passages.

Worker 1357 implemented this adaptation of Worker 135's published
`BorelExistence` construction. Workers 1354, 1293, 135, and 1357 identified
the relative containment interface and restricted minimization route.
The module does not change the host statement or its imports. It supplies
the containment construction needed for a separate exact proof of
`SolvableSubgroupBorelContainmentStatement`; that exact proof is not part of
this module. It assumes no Borel conjugacy, maximal-torus conjugacy, or
torus splitting theorem. These remain separate obligations for the host
maximal-torus conjugacy theorem.
