# Semisimple root generation from explicit structural inputs

Worker 1437.

`semisimpleRootGenerationIso` constructs an actual group-scheme isomorphism
`D ≅ G` for a closed subgroup `d : D → G` of a semisimple group over any
field `k : Type u`, in arbitrary characteristic. The chosen torus
`i : T.toGrp → G` is split and closed. The subgroup contains every intrinsic
relative-root functor for `i`. Two structural premises are explicit:
`RelativeRoot.HasOppositeFactorPairs i` and the all-test equality
`torusCentralizer i = SubgroupFunctor.range i`.
Maximality and algebraic closure are unnecessary for this pointwise
construction. Smoothness and connectedness of `D` are unnecessary.
The separate monomorphism and affineness instances in its declaration
follow from closedness of `i` and semisimplicity of `G`.

The companion `semisimpleRootGenerationIso_hom` identifies its forward
homomorphism with the original `d`.
`IsSemisimple.range_eq_top_of_oppositeFactorPairs_of_selfCentralizing`
is the underlying fullness theorem. All containment and fullness concern
every test scheme, including nonreduced tests.

The implemented proof composes two internal constructions:

1. `IsSemisimple.range_torus_le_of_oppositeFactorPairs` puts the entire
   torus range in `D`, using the supplied actual opposite pairs and the
   containment of every intrinsic root functor.
2. `range_eq_top_of_selfCentralizing_torus_and_rootSubgroups` gives full
   range. Its supplied self-centralization equality bounds the zero
   adjoint weight by the torus tangent image. Smooth connected generation
   by the torus and actual root representatives then has full Lie image.
   Minimality among all closed subgroups gives fullness of `D`.
3. The uniqueness of representatives of the top subgroup functor gives
   the actual isomorphism and its forward-map identity.

`SemisimpleRootGenerationReductionStatement` is the proposition

```text
RootRankOneFactorizationStatement.{u} →
  AlgClosedMaximalTorusCentralizerStatement.{u} →
    SemisimpleRootGenerationStatement.{u}.
```

`semisimpleRootGenerationReduction` proves it for every universe `u`.
For the actual split maximal torus in the published target, maximality
as a split torus follows from maximality as a torus. The supplied existing
rank-one statement yields the required opposite pair for every nonidentity
rational root point by projecting its unique-existence clause. The other
supplied statement gives all-test self-centralization. The pointwise
fullness theorem therefore proves exactly the published root-generation
conclusion, retaining both inputs as hypotheses.

The provenance is internal composition of the imported geometric
constructions and existing proposition targets; no new literature
assertion is introduced. The published target and all its imports remain
unchanged. This module proves neither rank-one factorization nor
maximal-torus self-centralization unconditionally. It is a conditional
bridge toward the host almost-simple-generation proof and does not
complete that task.
