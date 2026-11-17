# Openness of multiplicative-type charts

Module `Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartOpen`, namespace
`Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart`.

Author: Worker 57.

This is an internal module for the chart construction of Task 6946. It proves that every
window datum `dw` (`MixedChartExistence.WindowDatum`) has a chart `j G dw.toDatum` satisfying
`MultiplicativeTypeSubgroupModuli.IsOpenChartOnAffines`. The main condition is openness: for
a closed multiplicative-type subgroup `i` over an affine test `T`, the locus of `T` where `i`
is an evaluation of the chart is open. The module follows the Library module
`HomScheme.TorusChartOpen`, with these changes:

- étale splittings of tori are replaced by fppf splittings of groups of multiplicative type;
- split-torus Hopf points of rank `I` are replaced by diagonalizable Hopf points with an
  arbitrary character group `Λ'`;
- the window lattice `ℤ^r` is replaced by `ℤ^r × F`.

The general lemmas of `TorusChartOpen` (`evaluate_eq_of_comp_fpqc`, `injective_all_of_affine`,
`exists_evaluate_of_openCover`) do not mention tori and are reused from the Library. The
étale descent step `exists_good_open_of_etale` is replaced by Worker 872's flat version
`FppfParameterDescent.exists_good_open_of_flat`.

## The splitting hypothesis

`FppfSplitStatement` is a `Prop`-valued definition, used as the hypothesis `hP3` below. Let
`G` be an affine group over `Spec R` and `i : L → G_T` a closed subgroup over an affine test
`T`, with `L` of multiplicative type (`RelativeMultiplicativeType.IsMultiplicativeType`). The
statement asserts finitely many `R`-algebras `C k` with maps `b k : Spec (C k) → T` that are
flat and locally of finite presentation and jointly cover `T`. It also asserts finitely
generated commutative groups `Λ k` and Hopf points `f k : A → C k ⊗ R[Λ k]` with surjective
linear extensions. Finally, the evaluation of `i` at `b k` is the range of the homomorphism
`(diagPointEquiv G (C k)).symm (f k)` from `D(Λ k)`.

This is verbatim the conclusion of Worker 872's theorem `HomScheme.exists_fppf_diagPoints`
(module `HomScheme.MultiplicativeTypeSubgroupSplitting`). The final proof discharges `hP3`
with that theorem.

## Ring-level lemmas (section `Generic`, arbitrary coordinate algebra `A`)

- `toAlgHom_W_Bf`, `isUnit_algebraMap_Bf_N_mul_f`: `W → B_f` factors through `B`, and `N f`
  becomes a unit in `B_f`.
- `exists_local_lift` (ring-level openness, `maxHeartbeats 1000000`): the inputs are a Hopf
  point `α' : A → C[ℤ^r × F]`, a field point `ψ : C → K`, and a point `yK` of `B_f` such
  that the specialization of `α'` along `ψ` is the window Hopf point at `yK`. Then there is
  `g` with `ψ g ≠ 0` such that, over `C_g`, `α'` is the window Hopf point at some point `b''`
  of `B_f` with values in `C_g`. The proof is that of the torus version with the boxes
  `mbox r F n` and the reduction `mred r F m`:
  1. The weights of `α'` at the residue field of `ker ψ` lie in the box, so
     `exists_away_weightsIn` gives `g₁` with the weights in the box over `C_{g₁}`.
  2. The reduction of `α'` over `C_{g₁}` is `pointOf w₁` for a point `w₁` of `W`
     (`MixedChartExistence.exists_point_of_hopfPoint`). At `ψ` it agrees with the point under
     `yK` (`pointOf_injective`).
  3. Inverting a numerator `w₂` of `w₁ (N f)` makes `w₁` factor through `B_f`, giving `b''`.
  4. Over `C_{g₁ w₂}`, both `α'` and the window Hopf point at `b''` extend `pointOf w` with
     generator values in the box. By uniqueness of extensions
     (`existsUnique_hopfPoint_extension`, using `dw.injOn`) they are equal.

## Local lemmas (section `Local`, `A = O(G)`)

- `range_twist_eq`: twisting a closed Hopf point `f : A → C ⊗ R[Λ']` by an isomorphism
  `T : Λ' ≅ ℤ^r × F` does not change the range of the attached homomorphism
  (`range_diagPointEquiv_symm_eq_iff_ker₂` and the Library's
  `TorusChartRing.ker_scalarExt_mapDomain_addEquiv₂`).
- `exists_twist_of_range_eq`: over a field `K`, let `f` be a closed Hopf point of `D(Λ')` with
  the same range as the window subgroup at a point `b'` of `B_f`. Then `f` is a twist of the
  window point: some `T : Λ' ≅ ℤ^r × F` turns `f` into the window Hopf point at `b'`. Equal
  ranges give equal kernels. Then `HopfPointConnected.exists_tau_of_ker_le` and
  `exists_addEquiv_of_comp` apply, since a field has only trivial idempotents.
- `evaluate_comp_of_eq_range`: if `evaluate i bk` is the range of the homomorphism of `fk`,
  then after precomposition with `specMap g` it is the range of the homomorphism of the
  pushed point.
- `exists_piece_lift` (`maxHeartbeats 1000000`): the setting is as follows.
  - `bk : Spec C → T` is a piece of an fppf splitting on which `i` is the closed subgroup of
    `fk`.
  - `x' : C → K` and `y' : B_f → K` are field points at which `fk` and the window subgroup
    have the same range.

  Then some `g` with `x' g ≠ 0` and some `b''` satisfy: on `Spec C_g`, the evaluation of `i`
  equals the evaluation of the chart at `b''`. Twist `fk` to `ℤ^r × F`
  (`exists_twist_of_range_eq`, `range_twist_eq`), then apply `exists_local_lift`.
- `exists_good_open` (needs `hP3`): let `b : T' → T` with `T` affine, and `a` a parameter of
  the chart with `evaluate j a = evaluate i b`. Then every point `b t'` has an open
  neighbourhood `W ⊆ T` carrying a parameter whose evaluation is `i` on `W`. Proof:
  1. Split `i` fppf-locally by `hP3` and choose the piece `bk` through `b t'`.
  2. Find a field point of `Spec C_k ×_T T' ×_U D(f)` over `t'`, using that
     `p : D(f) → U` is surjective.
  3. At this field point the evaluation of `i` at `bk` and the window subgroup agree, so
     `exists_piece_lift` gives a principal open `Spec C_g` of the piece with a parameter.
     It contains a point over `b t'`, and `Spec C_g → T` is flat and locally of finite
     presentation.
  4. Conclude with `FppfParameterDescent.exists_good_open_of_flat` and chart injectivity
     (`injective_affine`).
- `isOpen_affine` (needs `hP3`): the openness condition on affine targets. `V'` is the union
  of all opens `W ⊆ T` that carry a parameter whose evaluation is `i` on `W`. If a parameter
  exists over `T'`, the image of `T'` lies in `V'` by `exists_good_open`. Conversely, local
  parameters on an open cover of `T'` glue (`TorusChart.exists_evaluate_of_openCover`).
- `smooth_qR_of_algebraSmooth`: if `W` is a smooth `R`-algebra, the chart is smooth over
  `Spec R` (`smooth_qR`).
- `isOpenChartOnAffines` (needs `hP3` and `[Algebra.Smooth R W]`): every window chart is an
  open chart on affine tests in the sense of
  `MultiplicativeTypeSubgroupModuli.IsOpenChartOnAffines`. The fields are
  `isClosedSubgroup_j`, `isMultiplicativeType_K`, `smooth_qR_of_algebraSmooth`,
  `injective_affine` and `isOpen_affine`.

## Provenance

Internal infrastructure, ported from the Library module `HomScheme.TorusChartOpen`. The
openness of the charts is the openness step in the proof of SGA 3, Exp. XI, Théorème 4.1,
for subgroups of multiplicative type. There, fppf descent replaces the étale splitting of
tori.
