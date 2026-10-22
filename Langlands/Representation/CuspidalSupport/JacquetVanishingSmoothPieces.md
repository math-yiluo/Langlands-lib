# Smooth representatives of geometric pieces

Authors: Worker 191, with Worker 169's integration design.

This module constructs smooth representatives of the geometric-piece functors
already defined in `Langlands.Representation.Geometric.GeometricLemmaStatement`.
Its provenance is internal and derived: it retains the smoothness information
in the existing composite rather than introducing a new representation-theoretic
assertion.

For block shapes `B` and `C` of the same rank, a permutation `w`, source
refinement `S`, target refinement `R`, and the two displayed subgroup
equalities, `geometricPieceInducingFunctor` composes normalized source Jacquet,
source equality relabeling, the existing inverse-conjugation transport, and
target equality relabeling. Its output is an actual smooth representation of
the target refined Levi. `geometricPieceSmoothFunctor` then applies the existing
normalized refined induction functor into the target Levi.

`geometricPieceSmoothFunctor_toRep` proves by reflexivity that forgetting the
constructed smoothness returns exactly the existing `geometricPieceFunctor`.
`geometricPieceSmoothFunctor_obj_toRep` evaluates that equality at a source
object to identify the resulting representation, including its carrier and
action. These are equalities of the actual constructions.

The construction allows every prime, actual p-adic field with compatible
topological data, and rank, including rank zero. The field universe `uF` and
source-carrier universe `uV` are independent. The inducing object remains in
carrier universe `uV`; the induced object lies in `max uF uV`. The source object
is an arbitrary smooth complex representation. No quasicuspidality,
admissibility, finite length, or positive-rank hypothesis is needed.

This auxiliary definition unit provides smooth representatives for use with
filtration and induction statements. It asserts neither the geometric lemma
nor either Jacquet-vanishing target. The conditional proper-induction bridge
and the incomplete final vanishing assembly are separate private drafts.
