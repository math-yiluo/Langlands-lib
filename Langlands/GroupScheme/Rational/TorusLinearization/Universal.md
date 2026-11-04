# Stable subspaces, fixed polynomials and the universal point

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

- `coeffMap_smul_map`, `coeffMap_mem_span`: applying a linear map `l : B → S` to the
  coefficients sends the `B`-span of the images of a set `W` of polynomials over `k` into the
  `S`-span of the images of `W`.
- `mem_of_map_mem_span` (descent of membership): if the image over `K` of a polynomial `f`
  over `k` lies in the `K`-span of the images of a `k`-subspace `N`, then `f ∈ N`. The proof
  applies a form `θ` with `θ 1 = 1` to the coefficients.
- `PointAction.Stable W`: for every `k`-algebra `B` and every point `t` over `B`, the pullback
  along `t` sends `W` into the `B`-span of the images of `W`.
- `PointAction.fixed p`: the polynomials in `addSpan n k p` (the span of the `X_j^(p^r)`) that
  every point fixes. `stable_fixed` says this subspace is stable.
- The universal point is `σ (univUnits K I)` over the group algebra `K[I → ℤ]`, whose
  coordinate units are the basis characters (`charOf_univUnits`). `coeffMap_pullK_univ` says
  that taking the coefficient of the character `ψ` in its pullback gives the weight-`ψ`
  component `comp ψ`.
- Consequences:
  - `comp_map_mem_span`: the components of the image over `K` of a stable subspace stay in its
    `K`-span.
  - `comp_map_fixed`: fixed polynomials have weight zero.
  - `coeffMap_mem_fixed`: if `h ∈ addSpan n K p` has weight zero, then applying any `k`-linear
    form on `K` to its coefficients gives a fixed polynomial.
  - `mem_span_fixed`: such an `h` is in the `K`-span of the images of the fixed polynomials. The
    proof expands its coefficients in a `k`-basis of `K`.
