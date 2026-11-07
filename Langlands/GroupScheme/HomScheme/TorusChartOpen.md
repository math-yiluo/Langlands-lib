# Openness of torus charts

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. It proves that the chart `j G d.toDatum`
of every window datum `d` (`TorusChartExistence.WindowDatum`) satisfies the
Library's `TorusSubgroupModuli.IsOpenChartOnAffines`. The main new condition
is openness: for a closed torus subgroup `i` over an affine test `T`, the
locus of `T` where `i` is an evaluation of the chart is open.

## The splitting hypothesis

`EtaleSplitStatement` is a `Prop`-valued definition, used as a hypothesis
`hP3` by the theorems below. Let `G` be an affine group over `Spec R` and
`i : L → G_T` a closed relative-torus subgroup over an affine test `T`. The
statement asserts finitely many `R`-algebras `C k`, with étale maps
`b k : Spec (C k) → T` jointly covering `T`, and closed split-torus Hopf
points `f k : A → C k ⊗ R[ℤ^{I k}]` (with surjective linear extension). The
evaluation of `i` at `b k` is the range of the split-torus homomorphism of
`f k`.

This is verbatim the statement of Worker 950's published theorem
`HomScheme.exists_etale_splitPoints` (module
`Langlands.GroupScheme.HomScheme.TorusSubgroupSplitting`). The final proof
module `SmoothTorusSubgroupRepresentabilityProof` discharges `hP3` with that
theorem.

## General lemmas (any base `S₀`)

- `evaluate_eq_of_comp_fpqc`: equality of evaluations of two closed families
  descends along a quasi-compact, flat, surjective map of test objects. This
  uses the Library's `SubgroupFunctor.range_eq_of_baseChange_eq`.
- `injective_all_of_affine`: if a family is injective on affine tests, it is
  injective on all tests. Compare the two parameters on the affine cover of the
  test.
- `exists_evaluate_of_openCover`: given injectivity on affine tests, local
  parameters along an open cover of a test glue to a global parameter. On
  overlaps the local parameters agree by injectivity, so they glue
  (`glueMorphisms`). The glued parameter has the right evaluation, which can
  be checked on the cover (`evaluate_eq_iff_openCover`).
- `exists_good_open_of_etale`: let `e : E → T` be an étale map of affine
  tests, and `aE` a parameter over `E` matching `i` pulled back to `E`. Then
  every point of the image of `e` has an open neighbourhood `W` with a
  parameter matching `i` on `W`. Proof:
  1. Take a basic open `W` inside the open image of `e`.
  2. `E ×_T W → W` is a quasi-compact, flat surjection, hence an effective
     epimorphism.
  3. The parameter is compatible on `(E ×_T W) ×_W (E ×_T W)` by injectivity,
     so it descends to `W` (`EffectiveEpi.desc`).
  4. Its evaluation is correct by `evaluate_eq_of_comp_fpqc`.

## Local lemmas (base `Spec R`, `A` the coordinate algebra of `G`)

- `range_twist_eq`: twisting a closed split Hopf point by an isomorphism of
  character lattices `ℤ^I ≅ ℤ^r` does not change the range. This uses
  `SplitTorusRangeKernel.range_splitPointEquiv_symm_eq_iff_ker₂` and
  `ker_scalarExt_mapDomain_addEquiv₂`.
- `exists_twist_of_range_eq`: over a field `K`, a closed split Hopf point `f`
  of rank `I` with the same range as the window torus at a point `b'` of `B_f`
  is a twist of it. Some `T : ℤ^I ≅ ℤ^r` turns `f` into the window Hopf point
  at `b'`. Equal ranges give equal kernels. Then
  `HopfPointConnected.exists_tau_of_ker_le` and `exists_addEquiv_of_comp`
  apply, since a field has only trivial idempotents.
- `toAlgHom_W_Bf`, `isUnit_algebraMap_Bf_N_mul_f`: `W → B_f` factors through
  `B`, and `N f` becomes a unit in `B_f`.
- `exists_local_lift` (ring-level openness): let `α' : A → C[ℤ^r]` be a Hopf
  point, `ψ : C → K` a field point, and `yK` a point of `B_f` such that the
  specialization of `α'` along `ψ` is the window Hopf point at `yK`. Then
  some `g` with `ψ g ≠ 0` has the following property: over `C_g`, `α'` is the
  window Hopf point at some point `b''` of `B_f` with values in `C_g`. Proof:
  1. Weights descend: the weights of `α'` at the residue field of `ker ψ` lie
     in the box (`dw.weights`, `weightsIn_of_mapAlgHom`).
     `exists_away_weightsIn` gives `g₁` with the weights in the box over
     `C_{g₁}`. The generator values are then supported in the box.
  2. The reduction modulo `m` of `α'` over `C_{g₁}` is `pointOf w₁` for a
     point `w₁` of `W` (`exists_point_of_hopfPoint`). At `ψ`, `w₁` agrees
     with the point of `W` under `yK` (`pointOf_injective`).
  3. `N f` is invertible at `yK`, so `w₁ (N f)` is nonzero at `ψ`. Writing
     `w₁ (N f) = w₂ / g₁^k` and inverting `g₁ w₂` makes `w₁` factor through
     `B_f`, giving `b''`.
  4. Over `C_{g₁ w₂}`, both `α'` and the window Hopf point at `b''` extend
     `pointOf w` with generator values in the box. By uniqueness of
     extensions (`existsUnique_hopfPoint_extension`, using `dw.injOn`) they
     are equal.

  The proof needs `maxHeartbeats 1000000`.
- `ofGroupAlgebra_toGroupAlgebra`: the two forms of a point are inverse.
- `evaluate_comp_of_eq_range`: if `evaluate i bk` is the range of the
  split-torus homomorphism of `fk`, then after precomposition with
  `specMap g` it is the range of the homomorphism of the pushed point.
- `exists_piece_lift` (`maxHeartbeats 1000000`): the setting is as follows.
  - `bk : Spec C → T` is a piece of an étale splitting, on which `i` is the
    closed split torus of `fk`.
  - `x' : C → K` and `y' : B_f → K` are field points at which `fk` and the
    window torus have the same range.

  Then some `g` with `x' g ≠ 0` and some `b''` satisfy: on `Spec C_g`, the
  evaluation of `i` equals the evaluation of the chart at `b''`. Twist `fk` to
  rank `r` (`exists_twist_of_range_eq`, `range_twist_eq`), then apply
  `exists_local_lift`.
- `exists_good_open` (needs `hP3`): let `b : T' → T` with `T` affine, and `a`
  a parameter of the chart with `evaluate j a = evaluate i b`. Then every
  point `b t'` has an open neighbourhood `W ⊆ T` with a parameter whose
  evaluation is `i` on `W`. Proof:
  1. Split `i` étale-locally by `hP3`. Choose the piece `bk` through `b t'`.
  2. Find a field point `Spec K` of `Spec C_k ×_T T' ×_U D(f)` over `t'`, a
     residue field of an iterated pullback. Here `p : D(f) → U` is
     surjective.
  3. At this field point, the evaluation of `i` at `bk` and the window torus
     agree. `exists_piece_lift` gives a principal open `Spec C_g` of the piece
     with a parameter. It contains the point over `b t'`.
  4. Conclude with `exists_good_open_of_etale` and chart injectivity
     (`injective_affine`).
- `isOpen_affine` (needs `hP3`): the openness condition on affine targets.
  Take `V'` to be the union of all opens `W ⊆ T` carrying a parameter whose
  evaluation is `i` on `W`. If a parameter exists over `T'`, then the image of
  `T'` lies in `V'` by `exists_good_open`. Conversely, if the image lies in
  `V'`, the local parameters on the preimages glue by
  `exists_evaluate_of_openCover`.
- `smooth_qR_of_algebraSmooth`: if `W` is a smooth `R`-algebra, the chart is
  smooth over `Spec R` (`TorusChartConstruction.smooth_qR`).
- `isOpenChartOnAffines` (needs `hP3` and `[Algebra.Smooth R W]`): every
  window chart is an open chart on affine tests. The fields are
  `isClosedSubgroup_j`, `isTorus_K`, `smooth_qR_of_algebraSmooth`,
  `injective_affine` and `isOpen_affine`.
