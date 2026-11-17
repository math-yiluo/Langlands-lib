# The quotient chart of a ring-level multiplicative-type chart datum

Module `Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartConstruction`, namespace
`Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart`.

Author: Worker 57.

This is an internal module for the chart construction of the task "Prove that
multiplicative-type subgroups of a fibre lift to an étale neighbourhood" (Task 6946). It is
the multiplicative-type analogue of the Library module `HomScheme.TorusChartConstruction`,
whose proofs it follows step by step. The character lattice `ℤ^r` becomes
`Λ = ℤ^r × F`, with `F` a finite commutative group. The split torus becomes the
diagonalizable group `D(Λ)`.

From a chart datum `d : MixedChartRing.Datum R A r F m gen n` the module builds two things:

- the chart `U d`, the quotient of `Spec B` (`B = W_N`) by the free twisting action of
  `Γ = Aut((ℤ/m)^r × F)`;
- a closed subgroup `j G d` of multiplicative type of the pulled-back ambient group over `U d`.

Here `W = MixedChartAlgebra.W R A ((ℤ/m)^r × F)` represents Hopf points of
`D((ℤ/m)^r × F)`. `G` is an affine group scheme over `Spec R` whose coordinate Hopf algebra
`A = AffineCoordinates.hopfAlgebra G` is finitely presented. `j G d` is the descent, along the
étale cover `D(f) → U d`, of the diagonalizable subgroup defined by the window Hopf point
`d.α : A → B_f[Λ]`.

## The quotient chart (generic coordinate algebra `A`)

- `X d := Spec B`. `action d` is the free action of `Γ` built from `d.actB` and `d.actB_free`
  by the Library's `SpecRingAction.finiteFreeSchemeAction`. `action_act_hom` records that `γ`
  acts by `Spec.map (actB γ)`.
- `quot d`: the Library's affine quotient `FiniteFreeSchemeAction.quotient`. Its quotient map
  is finite, étale and surjective, and the action relation is its kernel pair.
- `toBase d : Spec B → Spec R`, `act_comp_toBase`, and the descended structure map `qR d` of
  the quotient (`map_qR`). `U d := Over.mk (qR d)` is the chart.
- `Bf d := B_f`, the window piece `S d := specOver R (Bf d)`, its inclusion `ι d` into
  `Spec B`, and the map `uS d : W_f → B_f` (`uS_comp`).
- `p d := ι d ≫ quotient map : D(f) → U d`, with `p_qR`. `pOver d` is the same map as a
  morphism over `Spec R`. `p d` is flat, locally of finite presentation and étale, as an open
  immersion followed by the quotient map.
- `exists_act_mem_range`: every point of `Spec B` has a translate in `D(f)`. This is
  `d.cover` applied to the prime of `W` under the point.
- `Surjective (p d)` follows, since the quotient map is surjective and invariant.
- `exists_act_of_comp_eq`: two points `x₁, x₂ : Spec C → Spec B` over a local ring `C` with
  the same image in the quotient differ by a single `γ`. The pair lifts to the action relation,
  a coproduct of copies of `Spec B` indexed by `Γ`. `Spec C` is connected (the Library's
  `TorusChart.connectedSpace_spec_of_isLocalRing`), so the lift factors through one summand
  (`connectedHom_factor_coproduct`).
- `actB_eq_of_spec_eq`: the ring form of the previous lemma, by faithfulness of `Spec`.
- `exists_actB_of_specMap`: for two `R`-points `a', b'` of `B_f` with the same image in
  `U d`, after localizing `C` at any maximal ideal `P` the induced points of `B` differ by some
  `actB γ`.
- `ker_pushα_uS_eq`: in that situation the scalar extensions of `d.pushα (a' ∘ uS)` and
  `d.pushα (b' ∘ uS)` have the same kernel. Kernels can be compared after localizing at every
  maximal ideal (`HopfPointClosedLocus.ker_scalarExt_eq_of_localization`), and there
  `Datum.ker_pushα_eq` applies.
- `smooth_qR`: if `Spec W → Spec R` is smooth, so is the chart. `Spec B` is open in `Spec W`,
  and smoothness descends along the étale surjection `Spec B → U d` (the Library's
  `smoothEtaleSourceDescent`).

## The descended subgroup (`A = O(G)`)

- `fS G d`: the window Hopf point `d.pushα (uS d)` over `B_f`, in tensor form (Library
  `TorusChartRing.ofGroupAlgebra`). `iS G d := (diagPointEquiv G (Bf d)).symm (fS G d)` is the
  corresponding homomorphism `D(Λ) → G` over the window piece
  (`HomScheme.DiagonalizableHopfPoint`).
- `toGroupAlgebra_pushPoint_fS`, `surjective_pushPoint_fS`,
  `liftEquiv_pushPoint_fS_eq_zero_iff`, `surjective_fS`: specializing `fS` along
  `g : B_f → C` gives the Hopf point `d.pushα (g ∘ uS)`. These specializations are closed
  immersions, and their kernels are the kernels of the scalar extensions of `d.pushα (g ∘ uS)`.
- `isClosedSubgroup_iS`: `iS` is a closed subgroup (`isClosedSubgroup_diagPointEquiv_symm_iff`).
- `evaluate_iS_specMap`: the evaluation of `iS` at `specMap a'` is the range of the specialized
  homomorphism (`evaluate_diagPointEquiv_symm_eq_range`).
- `range_pushPoint_fS_eq`: two specializations with the same kernel have the same range
  (`range_diagPointEquiv_symm_eq_iff_ker`).
- `evaluate_iS_eq`: two points `a, b : specOver R C → S d` with `a ≫ p = b ≫ p` give the same
  evaluation of `iS`. This combines `exists_actB_of_specMap`, `ker_pushα_uS_eq` and
  `range_pushPoint_fS_eq`.
- `isClosedSubgroup_i`, `overlap_eq`: `iS`, transported to the pullback of `G` along `qR`,
  satisfies the descent overlap condition along `p`. The proof uses
  `TorusChartDescent.overlap_range_eq_of_evaluate_eq` and `evaluate_eq_of_specOver`, with the
  relation `a ≫ p = b ≫ p`.
- `exists_descent`: by the Library's `IsClosedSubgroup.exists_descent_of_overlap_range_eq`,
  there is an affine closed subgroup `H₀` of `G` over `U d`, together with an isomorphism from
  its pullback along `p` to the base change of `D(Λ)`. Under this isomorphism the pullback of
  the inclusion becomes `iS`.
- `K G d`, `j G d`, `recovery G d`: the chosen descended group, its inclusion and the recovery
  isomorphism, with `isAffine_K`, `isClosedSubgroup_j` and `baseChange_j`.
- `evaluate_j_comp_pOver`: at test points through the window piece, the evaluation of `j` is
  the evaluation of `iS`.
- `isMultiplicativeType_K`: `K G d` is of multiplicative type in the sense of the Library's
  `RelativeMultiplicativeType.IsMultiplicativeType`, an fppf cover with diagonalizable pieces.
  The cover is the single morphism `p d` (`Scheme.Hom.cover` for `Flat ⊓ LocallyOfFinitePresentation`;
  `p d` is surjective). The pullback of `K G d` along `p d` is isomorphic, via `recovery` and
  the Library's `diagonalizableBaseChangeIso`, to `D(Λ)` over the window piece. `Λ` is finitely
  generated (`Module.Finite.iff_addGroup_fg`).

## Provenance

Internal infrastructure. It follows the Library module `HomScheme.TorusChartConstruction`
with `ℤ^r` replaced by `ℤ^r × F` and split tori replaced by diagonalizable groups. The
mathematics is the chart construction in the proof of SGA 3, Exp. XI, Théorème 4.1, for
subgroups of multiplicative type.
