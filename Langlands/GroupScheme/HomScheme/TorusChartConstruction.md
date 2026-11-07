# The quotient chart of a ring-level torus chart datum

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. From a chart datum
`d : TorusChartRing.Datum R A r m gen n` it builds the following:

- the chart `U d`, the quotient of `Spec B` (`B = W_N`) by the free twisting
  action of `Γ = Aut((ℤ/m)^r)`;
- a closed relative-torus subgroup `j G d` of the pulled-back ambient group
  over `U d`.

Let `G` be an affine group scheme over `Spec R` with coordinate Hopf algebra
`A = AffineCoordinates.hopfAlgebra G`, assumed finitely presented. Then `j G d`
is the descent, along the étale cover `D(f) → U d`, of the split torus defined
by the window Hopf point `d.α`.

## The quotient chart

- `connectedSpace_spec_of_isLocalRing`: the spectrum of a local ring is
  connected. Its clopen sets are basic opens of idempotents, and these are `0`
  or `1`.
- `X d := Spec B`. `action d` is the free action of `Γ`, made from
  `d.actB` and `d.actB_free` by Worker 1421's
  `SpecRingAction.finiteFreeSchemeAction`. `action_act_hom` records that
  `γ` acts by `Spec.map (actB γ)`.
- `quot d`: the Library's affine quotient
  `FiniteFreeSchemeAction.quotient`. The quotient map is finite, étale and
  surjective, and the action relation is its kernel pair.
- `toBase d : Spec B → Spec R`, with `act_comp_toBase`, and its descent
  `qR d` to the quotient (`map_qR`). `U d := Over.mk (qR d)` is the chart.
- `Bf d := B_f`, the window piece `S d := specOver R (Bf d)`, its inclusion
  `ι d` into `Spec B`, and the map `uS d : W_f → B_f` (`uS_comp`).
- `p d := ι d ≫ quotient map : D(f) → U d`, with `p_qR`. `pOver d` is the same
  map as a morphism over `Spec R`. `p d` is flat, locally of finite
  presentation and étale, as a composite of an open immersion and the
  quotient map.
- `exists_act_mem_range`: every point of `Spec B` has a translate in `D(f)`.
  This is `d.cover`, applied to the prime of `W` under the point.
- `Surjective (p d)`: the quotient map is surjective and invariant, so this
  follows from `exists_act_mem_range`.
- `exists_act_of_comp_eq`: two points `x₁, x₂ : Spec C → Spec B` over a local
  ring `C` with the same image in the quotient differ by a single `γ`. The pair
  `(x₁, x₂)` lifts to the action relation, a coproduct of copies of `Spec B`
  indexed by `Γ` (`isPullback`). `Spec C` is connected, so the lift factors
  through one summand (the Library's `connectedHom_factor_coproduct`).
- `actB_eq_of_spec_eq`: the ring form of the previous lemma, by faithfulness
  of `Spec`.
- `exists_actB_of_specMap`: for two `R`-points `a', b'` of `B_f` with the same
  image in `U d`, after localizing `C` at any maximal ideal `P` the induced
  points of `B` differ by some `actB γ`.
- `ker_pushα_uS_eq`: in that situation, the scalar extensions of the window
  Hopf points `d.pushα (a' ∘ uS)` and `d.pushα (b' ∘ uS)` have the same kernel.
  Kernels can be compared after localizing at every maximal ideal
  (`HopfPointClosedLocus.ker_scalarExt_eq_of_localization`), and there
  `Datum.ker_pushα_eq` applies.
- `smooth_qR`: if `Spec W → Spec R` is smooth, so is the chart. `Spec B` is
  smooth over `Spec R`, being open in `Spec W`. Smoothness descends along the
  étale surjection `Spec B → U d` (the Library's `smoothEtaleSourceDescent`).
- `hom_ext_of_localization`: two morphisms `Spec C → Y` to an affine scheme
  are equal if they agree after restriction to every `Spec C_P`, for `P`
  maximal.

## The descended torus

- `fS G d`: the window Hopf point `d.pushα (uS d)` over `B_f`, in tensor form.
  `iS G d` is the corresponding split-torus homomorphism over the window
  piece, `(SplitTorusPoint.splitPointEquiv G (Bf d)).symm (fS G d)`.
- `toGroupAlgebra_pushPoint_fS`, `surjective_pushPoint_fS`,
  `liftEquiv_pushPoint_fS_eq_zero_iff`, `surjective_fS`: specializations of
  `fS` along `g : B_f → C` are the Hopf points `d.pushα (g ∘ uS)`. They are
  closed immersions, with the same kernels.
- `isClosedSubgroup_iS`: `iS` is a closed subgroup, by the Library's
  `isClosedSubgroup_splitPointEquiv_symm_iff`.
- `evaluate_iS_specMap`: the evaluation of `iS` at `specMap a'` is the range
  of the specialized split-torus homomorphism (the Library's
  `evaluate_splitPointEquiv_symm_eq_range`).
- `range_pushPoint_fS_eq`: two specializations with the same kernel have the
  same range (the Library's `range_splitPointEquiv_symm_eq_iff_ker`).
- `evaluate_iS_eq`: two points `a, b : specOver R C → S d` with
  `a ≫ p = b ≫ p` give the same evaluation of `iS`. Combine
  `exists_actB_of_specMap`, `ker_pushα_uS_eq` and `range_pushPoint_fS_eq`.
- `isClosedSubgroup_i`, `overlap_eq`: `iS`, transported to the pullback of
  `G` along `qR`, satisfies the descent overlap condition along `p`. Use
  `TorusChartDescent.overlap_range_eq_of_evaluate_eq` together with
  `evaluate_eq_of_specOver`, the relation being `a ≫ p = b ≫ p`.
- `exists_descent`: by the Library's
  `IsClosedSubgroup.exists_descent_of_overlap_range_eq`, there is an affine
  closed subgroup `H₀` of `G` over `U d` and an isomorphism of its pullback
  along `p` with the split torus, under which the pullback of the inclusion is
  `iS`.
- `K G d`, `j G d`, `recovery G d`: the chosen descended group, its inclusion
  and the recovery isomorphism. Their properties are `isAffine_K`,
  `isClosedSubgroup_j` and `baseChange_j`.
- `evaluate_j_comp_pOver`: at test points through the window piece, the
  evaluation of `j` is the evaluation of `iS`.
- `isTorus_K`: `K G d` is a relative torus. Its pullback along the étale
  surjection `p` is isomorphic to a split torus (`IsSplitTorus.of_iso`).
