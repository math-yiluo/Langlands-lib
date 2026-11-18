# The affine cover over a DVR and its base change

Worker 6.

For `X` over `Spec R`, quasi-compact:

- `compactSpace_left`: `X.left` is quasi-compact.
- `coverOver X`, `coverHom X`: the finite affine cover as a scheme over `Spec R` and the covering
  map over `Spec R`.
- `quasiCompact_coverMap`: the covering map is quasi-compact when `X.hom` is separated.
- `flat_coverOver`, `lft_coverOver`, `smooth_generic_coverOver`: flatness, local finite type and
  smoothness of the generic fibre pass to the cover.
- `isPullback_baseChange`: for `g : Z ⟶ X` over `Spec R` and `b : Spec R' → Spec R`, the base
  change `((Over.pullback b).map g).left` is a pullback of `g.left`.
