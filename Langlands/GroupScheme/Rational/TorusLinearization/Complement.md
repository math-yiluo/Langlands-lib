# A stable complement of the fixed and higher additive polynomials

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

- `natCast_eq_zero_of_algebra`: `p = 0` in every algebra over a field of characteristic `p`.
- `pow_mem_of_mem_addSpan`: suppose `p = 0` in `B` and a `B`-submodule `N` contains every
  `X_l^(p^s)` with `s ≥ r`. Then `g^(p^r) ∈ N` for every `g` in the span of the `X_j^(p^r)`
  (`addSpan`). The proof is span induction with the additivity of the `p^r`-th power.
- `aeval_mem_addSpan`: substituting polynomials from `addSpan` into a polynomial from
  `addSpan` gives a polynomial in `addSpan`.
- `higher n k p`: the span of the `X_j^(p^r)` with `r ≥ 1`, that is, the additive polynomials
  without linear terms. It lies in `addSpan` (`higher_le_addSpan`).
- `span_map_id`: the `k`-span of a `k`-subspace, viewed through the identity map of
  coefficients, is the subspace itself.
- `sub_extend_mem_span`: let `ψ` be a `k`-linear map on polynomials over `k`, and let `N`
  contain every `X^m - ψ(X^m)` with `m ∈ s`. For every polynomial `g` over `B` supported on
  `s`, `g - ψ_B(g)` lies in the `B`-span of the images of `N`. Here `ψ_B` is the
  `B`-linear extension `extend B ψ`.
- `descend θ π'`: the `k`-linear map `f ↦ θ_*(π'(f_K))` built from a `K`-linear map `π'` on
  polynomials over `K` and a `k`-linear form `θ : K → k`. Here `f_K` is the image of `f` over
  `K`, and `θ_*` applies `θ` to coefficients. `coeffMap_tens_extend_map` says: extend `π'` to
  `K ⊗ B`, apply it to the image of `g`, then apply `θ ⊗ id` to the coefficients. The result
  is the extension of `descend θ π'` to `B`, applied to `g`.
- `complement p θ π'`: the polynomials in `addSpan` killed by `descend θ π'`.
- For a point action `a`:
  - `pull_X`, `pull_map`: the pullback of `X_j` is the `j`-th coordinate polynomial, and
    pullback commutes with base change of points.
  - `Stable.sup`: the sum of two stable subspaces is stable.
  - `pull_mem_addSpan`, `pullK_mem_addSpan`: pullbacks preserve `addSpan`, because the
    coordinate polynomials of a point are additive.
  - `stable_higher`: `higher` is stable. `fixHigher p := higher ⊔ fixed p` is stable
    (`stable_fixHigher`) and lies in `addSpan` (`fixHigher_le_addSpan`).
  - `comp_mem_addSpan`: the weight components preserve `addSpan n K p`. The proof uses the
    universal point.
  - `comp_mem_span_of_stable`: the `K`-span of the images of a stable subspace is preserved by
    every weight component.
  - `extend_pullK_σ`, `pull_descend`: if `π'` commutes with every weight component, then it
    commutes with pullback along split points over `K`-algebras. Hence `descend θ π'` commutes
    with pullback along every point `t` over a `k`-algebra `B`:
    `pull t (descend θ π' f) = (descend θ π')_B (pull t f)`. The proof passes to the split
    point over `K ⊗ B` induced by `t`. No multiplicativity of `θ` is needed.
  - `exists_projection`: there is a `K`-linear `π'` that is the identity on the `K`-span `Y_K`
    of the images of `fixHigher p`, has range in `Y_K`, and commutes with every weight
    component. This applies `exists_graded_projection` to `Y_K`, which is graded by
    `comp_mem_span_of_stable`.
  - Assume `θ 1 = 1` and that `π'` is the identity on `Y_K` with range in `Y_K`. Then
    `descend θ π'` is the identity on `fixHigher p` (`descend_of_mem_fixHigher`) and has range
    in it (`descend_mem_fixHigher`, by `coeffMap_mem_span` and `span_map_id`). Consequently:
    - `sub_descend_mem_complement`: `f - descend θ π' f ∈ complement p θ π'` for `f ∈ addSpan`;
    - `addSpan_le_complement_sup`: `addSpan ≤ complement p θ π' ⊔ fixHigher p`;
    - `complement_inf_fixHigher`: `complement p θ π' ⊓ fixHigher p = ⊥`.
  - `stable_complement`: if moreover `π'` commutes with every weight component, then
    `complement p θ π'` is stable. Let `f` be in the complement and `t` a point over `B`.
    Then `g := pull t f` lies in `addSpan n B p`, and by `pull_descend` the extension of
    `descend θ π'` kills `g`. By `sub_extend_mem_span` with `s` the exponents of `addSpan`,
    `g = g - (descend θ π')_B g` lies in the `B`-span of the images of the complement.
