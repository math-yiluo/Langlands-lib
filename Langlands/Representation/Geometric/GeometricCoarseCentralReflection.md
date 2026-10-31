# inverse-conjugation restriction for geometric pieces

This internal construction works with the actual
`Geometric.geometricPieceFunctor`. It assumes its actual source and target
Levi equalities, and constructs the restricted source action that its coarse
central characters detect. It does not assume whole-Levi conjugacy or a
geometric filtration. Field and representation universes are independent;
auxiliary coordinate homomorphisms work over an independently universed
commutative ring.

`inverseRefinedIntersectionHom` uses the equality identifications,
the inverse of the published actual intersection conjugation, and the other
equality identification. Its embedding formula is exactly inverse matrix
conjugation. `inverseCoarseScalarIntersectionHom` composes that map
with target coarse scalars inside the target refined Levi. Its embedding
is `p(w)^(-1) * C.blockScalar(a) * p(w)`.

`geometricPieceCoefficientEquiv` retains the actual source normalized
refined Jacquet module. The published equality-relabeling equivalence and the
actual inverse-conjugation action identify the middle coefficient of the
geometric piece with that Jacquet representation pulled back by the constructed
homomorphism. This is an actual representation equivalence, rather than an
assumed comparison or a selected replacement coefficient. All underlying
linear maps are the identity relabelings from the public constructions.

`geometricPiece_coarse_character_reflects` applies the actual
normalized-refined-induction evaluation reflection to the last induction of
the geometric piece. The just-constructed equivalence then transports the
result to the normalized source Jacquet action restricted along the actual
inverse-conjugated target coarse scalars. The target induction half modulus
has already been removed by the proved triviality on target coarse scalars;
the actual normalized source Jacquet action is retained.

These are internal constructions and consequences of public definitions,
with no new literature claim. They require no minimality, irreducibility,
temperedness, finite-dimensionality, rank bound or character extension. This
module does not identify inverse-conjugated scalars in fine tuple coordinates.
It supplies no fine full-central character, real-exponent projection,
strict exclusion of a Weyl branch, geometric-lemma theorem, isolation or Hom
comparison. The provenance is internal, and the implemented proofs use only the imported constructions and elementary intertwiner transport.

Worker 526 implemented this construction. Workers 359 and 430 supplied
coordinate, normalization and same-power transport guidance during the
parent Hom-comparison investigation. This attribution supplies no analytic
comparison result.
