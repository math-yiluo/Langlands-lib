# Proof: rigidity of central homomorphisms from groups of multiplicative type

Worker 738.

This module proves the published statement
[`MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md),
which is SGA 3, Exposé IX, Théorème 5.1 and Corollaires 5.2 and 5.3. The source is the
registered Gille–Polo 2009 recomposed edition (`sga3-expose-ix-gille-polo-2009`),
pp.48–50 (PDF pages 18–20). Its proof is assembled from published Library results:

- **5.1, case a)** (`S` locally noetherian): `exists_open_eq_of_locallyNoetherian` in
  [`CentralRigidityLocal`](CentralRigidityLocal.md). It follows the proof on p.48 and
  uses the Library's central infinitesimal uniqueness theorem
  `CentralInfinitesimalRigidity.centralInfinitesimalUniqueness` (SGA 3, IX, 3.4, for an
  arbitrary group `G`).
- **5.1, case b)** (`G` of finite presentation): the theorem
  `multiplicativeTypeCentralRigidityNoetherianReduction`, which proves
  `MultiplicativeTypeCentralRigidityNoetherianReductionStatement` (module
  `GroupScheme.Torus.MultiplicativeTypeCentralRigidityNoetherianReductionProof`). It
  states that case a) implies case b), the reduction of the source on p.49.
- **5.2**: `CentralRigidity.local_triviality_of_local_central_equality` (module
  `GroupScheme.Torus.CentralRigidityReduction`), which deduces local triviality from
  local central equality by comparing `u` with the zero homomorphism, as on p.49.
- **5.3, openness**: `HomEqualityOpenLocus.exists_open_fibre_eq_locus` (module
  `GroupScheme.HomEqualityOpenLocus`). If fibre equality of two homomorphisms at any
  point extends to an open neighbourhood, then the set of points where the fibres agree is
  an open `U`, and the two homomorphisms agree over `U`.
- **5.3, closedness**: the theorem `multiplicativeTypeTrivialLocusClosed`, which proves
  `MultiplicativeTypeTrivialLocusClosedStatement` (module
  `GroupScheme.Torus.MultiplicativeTypeTrivialLocusClosedProof`). For `G` separated, the
  set of points with trivial fibre is closed (source p.50).

## `multiplicativeTypeCentralRigidity`

`Langlands.GroupScheme.multiplicativeTypeCentralRigidity` has type
`MultiplicativeTypeCentralRigidityStatement.{u}`. The proof is as follows.

1. `hA` is case a) of 5.1 for every locally noetherian scheme, given by
   `exists_open_eq_of_locallyNoetherian`.
2. Fix `S`, `H`, `G` with `H` of multiplicative type, and the disjunction of the base
   hypotheses. Clause 5.1, packaged as `CentralRigidity.LocalCentralEquality H G`, is
   `hA` if `S` is locally noetherian. If instead `G` is locally of finite presentation,
   quasi-compact and quasi-separated over `S`, it is
   `multiplicativeTypeCentralRigidityNoetherianReduction` applied to `hA`.
3. Clause 5.2 is `CentralRigidity.local_triviality_of_local_central_equality` applied to
   clause 5.1.
4. For clause 5.3, let `G` be separated and `u : H ⟶ G`. A homomorphism is trivial
   (`f.hom.hom = 1`) exactly when it is the zero homomorphism
   (`CentralRigidity.hom_eq_one_iff_eq_zero`), and base change preserves zero
   (`CentralRigidity.baseChange_map_zero`). With these, clause 5.2 says that fibre
   equality of `u` and `0` at a point extends to an open neighbourhood. Then
   `exists_open_fibre_eq_locus u 0` gives an open `U` whose points are exactly the `s`
   with `u_s = 0`, that is, with `u_s` trivial, and such that `u_U = 0_U`, that is,
   `u_U` is trivial. The underlying set of `U` is the set in
   `multiplicativeTypeTrivialLocusClosed`, so it is closed.

The theorem has no hypotheses and adds no axioms. It uses only `propext`,
`Classical.choice` and `Quot.sound`.
