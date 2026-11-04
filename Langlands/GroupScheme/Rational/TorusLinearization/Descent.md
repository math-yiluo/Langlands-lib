# Descent tools from the splitting field

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

- `coeffMap l`: applies a linear map `l` to every coefficient of a polynomial. It preserves
  `restrictSupport` (`coeffMap_mem_restrictSupport`).
- `extend S ψ`: the `S`-linear extension, along the monomial basis, of an `R`-linear
  endomorphism `ψ` of `R[X]` to `S[X]`. `extend_map` says it agrees with `ψ` on polynomials
  that come from `R`.
- `exists_theta`: there is a `k`-linear form `θ : K → k` with `θ 1 = 1`, for any field
  extension `K/k` (finite or not).
- `tens B l : K ⊗[k] B → B` sends `c ⊗ b` to `l c • b`.
- `PointAction.pull_coeffMap` (descent principle): let `l` be a linear form on `K`, `t` a point
  over a `k`-algebra `B`, and `ext t` its image over `K ⊗[k] B`. Then pulling back the
  coefficientwise image `coeffMap l h` along `t` gives `coeffMap (tens B l)` of the pullback of
  `h` along `ext t`.
