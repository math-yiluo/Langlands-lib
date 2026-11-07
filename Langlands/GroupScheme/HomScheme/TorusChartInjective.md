# Injectivity of torus charts on affine tests

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. It proves the injectivity condition of
the Library's `TorusSubgroupModuli.IsOpenChartOnAffines` for the chart
`j G d` over `U d` built in `TorusChartConstruction`. Two affine test points of
the chart with the same evaluation are equal.

## Results

- `uS_algebraMap`: `uS d` restricted to `W` is the map `W → B → B_f`.
- `comp_p_eq_of_evaluate_eq`: let `a', b'` be two `R`-points of `B_f` with
  values in `C`. If the window torus `iS` has the same evaluation at
  `specMap a'` and at `specMap b'`, then the two points have the same image in
  the chart. Proof:
  1. Equal ranges of the closed split-torus homomorphisms mean equal kernels
     of their linear extensions (the Library's
     `range_splitPointEquiv_symm_eq_iff_ker`). So the window Hopf points
     `d.pushα (a' ∘ uS)` and `d.pushα (b' ∘ uS)` have scalar extensions with
     the same kernel.
  2. Morphisms `Spec C` → affine scheme can be compared after localizing at
     every maximal ideal `P` (`hom_ext_of_localization`). At `P`,
     `Datum.exists_act_of_ker_eq` gives `γ` with the two induced points of `W`
     related by `act γ`.
  3. Both points invert `N`, so the induced points of `B` are related by
     `actB γ` (`IsLocalization.ringHom_ext`).
  4. The quotient map is invariant
     (`FiniteFreeSchemeAction.AffineQuotient.invariant`), so the two images in
     the chart agree.
- `comp_p_eq_of_evaluate_eq_affine`: the same conclusion for any affine test
  object `T` and points `ya, yb : T → S d`. Identify `T` with
  `specOver R Γ(T, ⊤)` using `T.left.isoSpec`, transport the evaluations
  (`evaluate_eq_comp`), and cancel the isomorphism.
- `injective_affine`: for an affine test object `T` and points `a, b` of the
  chart `U d` with `evaluate (j G d) a = evaluate (j G d) b`, we have `a = b`.
  Proof:
  1. The window map `p : D(f) → U d` is an affine étale surjection. It is the
     principal-open inclusion `D(f) → Spec B` followed by the quotient map
     `(quot d).map`. That quotient map is finite, which makes `p` affine.
     However, `p` itself need not be finite, since finiteness need not survive
     restriction to a principal open. Pull back `p` first along `a`, then along
     the composite with `b`. Since `T` is affine and `p` is affine, both
     pullbacks are affine schemes. The composite `c` of the two projections to
     `T` composes two base changes of the étale (hence flat) surjection `p`,
     so it is flat and surjective, hence an epimorphism. Both `c ≫ a` and
     `c ≫ b` factor through `p`.
  2. The evaluations of `j` at these factorizations are evaluations of `iS`
     (`evaluate_j_comp_pOver`), and they are equal.
  3. `comp_p_eq_of_evaluate_eq_affine` gives `c ≫ a = c ≫ b`, and `c` is an
     epimorphism.
