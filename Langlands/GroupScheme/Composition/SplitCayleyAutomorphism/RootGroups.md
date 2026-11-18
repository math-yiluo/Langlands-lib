# Torus and root-group automorphisms of Zorn's split Cayley algebra

Coordinates on `R⁸` are `(a, u₁, u₂, u₃, v₁, v₂, v₃, b)` as in `SplitCayley.mulFun`.

- `Root`: the twelve roots of the diagonal torus; `uᵢ = eᵢ`, `vᵢ = -eᵢ` (short) and
  `lᵢⱼ = eᵢ - eⱼ` (long), with `e₁ + e₂ + e₃ = 0`.
- `rootFun α r`: the explicit root-group element `x_α(r)`, quadratic in `r` for short roots and
  linear for long roots. `isAutomorphism_rootFun` proves over every commutative ring that it fixes
  the unit and preserves the Zorn product; `rootFun_rootFun` gives the additive law.
- `rootMatrix`, `rootGL`: the same element as a matrix and as an element of `GL₈`, with
  `rootGL_add`, `rootGL_zero`, `isAutomorphism_rootGL`.
- `torusFun`, `torusGL s t`: the diagonal torus element `diag(1, s, t, s⁻¹t⁻¹, s⁻¹, t⁻¹, st, 1)`
  for units `s, t`, multiplicative in `(s, t)` (`torusGL_mul`) and an automorphism
  (`isAutomorphism_torusGL`).

`IsAutomorphism f` means `f` fixes Zorn's unit and preserves Zorn's product. The explicit formulas
were derived for this project (by solving for unipotent automorphisms tangent to each torus weight
space with a computer-algebra script); every identity is verified directly in Lean, so no outside
source is relied on.
