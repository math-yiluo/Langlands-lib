# Continuous cohomological corestriction

Author: Worker 22. This construction uses the published finite corestriction,
its proved refinement compatibility, and the source comparison with Mathlib's
actual continuous cohomology. No transfer compatibility is a parameter.

Let `k` be a commutative topological ring, `G` a compact topological group,
`A : DiscreteModule k G`, `H` an open subgroup, and `q` a natural number.
The module has discrete topology and a jointly continuous action. The scalar,
group, and coefficient types have arbitrary common universe `u`; degree zero
is included. Hausdorffness and total disconnectedness are not required by the
construction. In particular it applies to profinite groups and the supported
scalar choice `ULift.{u} ℤ`.

Write `C = ambientOpenNormalCore H`. The source diagram
`transferSourceDiagram A.toRep H q` has at `N` the ordinary cohomology of
`H / (H ∩ (C ∩ N))` with the corresponding fixed coefficients. Its arrows
are the genuine inflation maps. The normal subgroup `C ∩ N` lies in `H`.
`continuousCorestrictionCocone A H q` sends this stage first by
`finiteCorestriction` at `C ∩ N`, then by `finiteStageToContinuous` into the
underlying module of `continuousCohomology q A.toTopRep`. Its naturality proof
uses the independently proved `finiteCorestrictionRefinement` followed by the
refinement identity for `finiteStageToContinuous`.

`continuousCorestriction A H q` first applies the inverse of
`transferSourceComparisonIso A H q`, then the colimit descent of that cocone.
Its source is the underlying module of Mathlib's actual continuous cohomology
of `(A.restrict H.toSubgroup).toTopRep`; its target is the corresponding
continuous cohomology of `A.toTopRep`. It is a `ModuleCat k` morphism, hence
linear and additive. The finite source comparison is a proved isomorphism,
not an identification by definition. The construction does not assert a
continuous linear map between the topological cohomology objects.

`continuousCorestriction_core_stage` follows from the inverse comparison's
injection identity and the universal property of colimit descent. It says
that transfer after inflation from the stage `C ∩ N` is finite transfer
followed by ambient continuous inflation. For every open normal `N ≤ H`,
`finiteStageToContinuous_comp_corestriction` proves the same identity at `N`:

```
finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H N) q ≫
    continuousCorestriction A H q =
  finiteCorestriction A.toRep H N hNH q ≫ finiteStageToContinuous A N q.
```

The proof refines `N` to `C ∩ N`, uses the core-stage identity, and applies
finite-corestriction refinement and continuous inflation refinement.
Transitivity, coefficient naturality, and restriction followed by index
multiplication remain separate transfer-law obligations.

Provenance is derived from Serre, *Local Fields*, Greenberg translation (1979),
Chapter VII, Section 7, printed page 119 / PDF page 125 (finite-index
corestriction extending the coset norm), and Chapter X, Section 3, printed
page 154 / PDF page 160 (the inflation-indexed fixed-coefficient limit and
continuous-cochain interpretation). The explicit normal-core indexing,
categorical descent, and comparison with Mathlib's nested continuous cochain
model are implementation details proved in this module and its imported
construction and comparison modules. The cited Galois discussion motivates
the profinite case; the broader compact-group signature follows from the
implemented proofs.

Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
