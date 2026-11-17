# Injectivity of multiplicative-type charts on affine tests

Module `Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartInjective`, namespace
`Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart`.

Author: Worker 57.

This is an internal module for the chart construction of Task 6946. It proves the
injectivity condition of `MultiplicativeTypeSubgroupModuli.IsOpenChartOnAffines` for the
chart `j G d` over `U d` built in `MultiplicativeTypeChartConstruction`: two affine test
points of the chart with the same evaluation are equal. It follows the Library module
`HomScheme.TorusChartInjective`. The one structural change is that the ring-level part is
proved for an arbitrary coordinate algebra `A` (section `Generic`), and only afterwards
specialized to `A = O(G)`.

## Results

- `uS_algebraMap` (generic `A`): `uS d` restricted to `W` is the map `W → B → B_f`.
- `comp_p_eq_of_ker_eq` (generic `A`): let `a', b'` be two `R`-points of `B_f` with values in
  `C`. Suppose the window Hopf points `d.pushα (a' ∘ uS)` and `d.pushα (b' ∘ uS)` have scalar
  extensions with the same kernel. Then `specMap a' ≫ p d = specMap b' ≫ p d`. Proof:
  1. Morphisms from `Spec C` to an affine scheme can be compared after localizing at every
     maximal ideal `P` (the Library's `TorusChart.hom_ext_of_localization`). At `P`,
     `MixedChartRing.Datum.exists_act_of_ker_eq` gives `γ ∈ Γ` relating the two induced
     points of `W` by `act γ`.
  2. Both points invert `N`, so the induced points of `B` are related by `actB γ`
     (`IsLocalization.ringHom_ext` and `Datum.actB_algebraMap`).
  3. The quotient map is invariant (`FiniteFreeSchemeAction.AffineQuotient.invariant`), so the
     two images in the chart agree.
- `comp_p_eq_of_evaluate_eq`: if the window subgroup `iS` has the same evaluation at
  `specMap a'` and at `specMap b'`, the two points have the same image in the chart. Equal
  ranges of the two closed homomorphisms from `D(ℤ^r × F)` mean equal kernels of their linear
  extensions (`range_diagPointEquiv_symm_eq_iff_ker`). Hence the scalar extensions of the
  window Hopf points have equal kernels, and `comp_p_eq_of_ker_eq` applies.
- `comp_p_eq_of_evaluate_eq_affine`: the same conclusion for any affine test object `T` and
  points `ya, yb : T → S d`. Identify `T` with `specOver R Γ(T, ⊤)` through `T.left.isoSpec`,
  transport the evaluations (`evaluate_eq_comp`) and cancel the isomorphism.
- `injective_affine`: for an affine test object `T` and points `a, b` of the chart `U d` with
  `evaluate (j G d) a = evaluate (j G d) b`, we have `a = b`. The window map
  `p : D(f) → U d` is an affine étale surjection: a principal-open inclusion followed by the
  finite quotient map. Pull `p` back along `a`, and then along the composite with `b`. Both
  pullbacks are affine. The composite `c` of the two projections to `T` is flat and
  surjective, hence an epimorphism, and `c ≫ a` and `c ≫ b` both factor through `p`. The
  evaluations of `j` at these factorizations are evaluations of `iS`
  (`evaluate_j_comp_pOver`), and they are equal. `comp_p_eq_of_evaluate_eq_affine` then gives
  `c ≫ a = c ≫ b`, and `c` is an epimorphism.

## Provenance

Internal infrastructure, ported from the Library module `HomScheme.TorusChartInjective` to
character lattices `ℤ^r × F`. Mathematically, a point of the chart is determined by the
subgroup it parametrizes. This is the injectivity of the chart in the proof of SGA 3,
Exp. XI, Théorème 4.1.
