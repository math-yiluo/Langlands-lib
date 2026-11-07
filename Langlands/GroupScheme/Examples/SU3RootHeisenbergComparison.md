# Trace-compatible cocycles and quadratic root parameters

This module is pure field algebra. It identifies a Heisenberg group law built from a cocycle
`β : L → L → L` with the quadratic root parameters of the published module
`GroupScheme/Examples/SU3RootParameters`. Those parameters are pairs `(u, v)` with
`v + σ(v) = u σ(u)` and law `(u, v)(u', v') = (u + u', v + v' + u σ(u'))`, the law of
Kaletha–Prasad (2.7.2). The intended application is the multipliable root group of a
quasi-split group, whose published Heisenberg normal form
(`GroupScheme/Rational/RootHeisenbergNormalForm`) has a law of the same shape. This module
does not make that application.

Provenance: internal. The statements and proofs are elementary linear algebra over a
separable quadratic extension, developed for this project. Kaletha–Prasad (2.7.2) is context
only, through the published parameter group.

All declarations live in namespace `Langlands.GroupScheme.SU3Root`.

## Setting

`k` is a field and `L` a field with `Algebra k L`, `Algebra.IsQuadraticExtension k L` and
`Algebra.IsSeparable k L`. Write `σ` for the published `conjugation k L`, the unique
nonidentity `k`-automorphism of `L`. `rationalParameters k L` is the published parameter
group for the involution `σ` (`fieldInvolution k L`). `Parameters.traceZero` is its additive
subgroup of elements `w` with `w + σ(w) = 0`.

A function `β : L → L → L` is called trace compatible here if
`β (f x) y + β x (f y) = (f + σ f) β x y` for all `f`, `x` and `y`.

## Statements

- `exists_algebraMap_eq_of_conjugation_eq`: an element fixed by `σ` lies in the image of
  `k`.
- `exists_conjugation_ne`: some element `θ` has `σ θ ≠ θ`.
  `exists_ne_zero_add_conjugation_eq_zero`: some nonzero element has trace zero.
- `exists_eq_add_conjugation_of_linear`: every additive map `ψ : L → L` with
  `ψ (c y) = c ψ(y)` for `c ∈ k` is `ψ y = A y + B σ(y)` for some `A, B ∈ L`.
- `exists_eq_of_trace_compatible`: if `β` is additive in its second argument and trace
  compatible, then `β x y = A σ(x) y + B x σ(y)` for some `A, B ∈ L`. The characteristic is
  arbitrary.
- `eq_neg_conjugation_of_traceZero`: if all values `A σ(x) y + B x σ(y)` have trace zero,
  then `B = -σ(A)`.
- `normalizedCocycle k L A x y = A σ(x) y - σ(A) x σ(y)`, as an element of
  `Parameters.traceZero`. `coe_normalizedCocycle` gives its value.
- `exists_eq_normalizedCocycle`: let `β` be additive in its second argument, trace
  compatible, with values of trace zero, and not symmetric (`β x y ≠ β y x` for some `x`,
  `y`). Then `β = normalizedCocycle k L A` for some `A` with `A + σ(A) ≠ 0`.
- Section `Equiv`, for `A` with `hA : A + σ(A) ≠ 0`, writing `s = A + σ(A)`:
  - `heisenbergParameter hA w x`: the parameter `(x, -s⁻¹ w + A s⁻¹ x σ(x))`, for
    trace-zero `w` and `x ∈ L`. `first_heisenbergParameter` and
    `second_heisenbergParameter` give its coordinates. `conjugation_inv_trace`:
    `σ(s⁻¹) = s⁻¹`.
  - `heisenbergParameter_mul`: the product of the parameters of `(w, x)` and `(w', x')` is
    the parameter of `(w + w' + normalizedCocycle k L A x x', x + x')`.
  - `heisenbergCoordinates p = (-s p.second + A p.first σ(p.first), p.first)`, and
    `heisenbergEquiv hA`, the bijection `traceZero × L ≃ rationalParameters k L` with
    inverse `heisenbergCoordinates`. `heisenbergEquiv_apply` gives its values.
  - `heisenbergParameter_scale`: if `w' = a σ(a) w`, then the parameter of `(w', a x)` is
    `Parameters.scale a` of the parameter of `(w, x)`.
  - `heisenbergParameter_mem_central`: the parameter of `(w, x)` is in
    `Parameters.central` exactly when `x = 0`.
- `exists_heisenbergEquiv`. Let `β` be as in `exists_eq_normalizedCocycle`. Then there is a
  bijection `e : traceZero × L ≃ rationalParameters k L` with three properties.
  1. `e (w, x) * e (w', x') = e (w + w' + β x x', x + x')`.
  2. The first coordinate of `e (w, x)` is `x`.
  3. `e (w', a x) = Parameters.scale a (e (w, x))` whenever `w' = a σ(a) w`.

## Proofs

**Form of a trace-compatible function.** Put `ψ y = β 1 y`. Trace compatibility at
`(f, 1, y)` gives `β x y = (x + σ x) ψ(y) - ψ(x y)`. Substituting this into trace
compatibility at `f = c ∈ k` gives

`(x + σ x) (ψ(c y) - c ψ(y)) = 2 (ψ(c x y) - c ψ(x y))`.

If `2 = 0` in `L`, take `x` of trace one (published `traceOne_add_conjugate`). If `2 ≠ 0`,
take a nonzero `x` of trace zero and replace `y` by `x⁻¹ y`. Either way `ψ` is `k`-linear.

**Linear maps.** Choose `θ` with `σ θ ≠ θ`. Every `y` is `a + b θ` with
`b = (y - σ y)/(θ - σ θ)` and `a = y - b θ`. Both `a` and `b` are fixed by `σ`, so they lie
in `k` (Galois fixed field, Mathlib's `IsGalois.mem_range_algebraMap_iff_fixed`). Then
`ψ y = a ψ(1) + b ψ(θ)`. With `B = (ψ θ - θ ψ 1)/(σ θ - θ)` and `A = ψ 1 - B`, this equals
`A y + B σ(y)`. Substituting into the formula for `β` gives the form of `β`.

**Trace-zero values.** Evaluate at `(1, 1)` and at `(1, θ)`. With `P = A + σ(B)`, these give
`P + σ P = 0` and `P θ + σ(P) σ(θ) = 0`, hence `P (θ - σ θ) = 0` and `P = 0`.

**Nondegeneracy.** `β x y - β y x = (A + σ A)(σ(x) y - x σ(y))`, so a non-symmetric `β`
has `A + σ A ≠ 0`.

**The bijection.** The parameter equation `v + σ v = u σ u` holds because `w` has trace zero,
`σ(s⁻¹) = s⁻¹` and `A s⁻¹ + σ(A s⁻¹) = 1`. The product formula, the two inverse identities
and the scaling identity are ring identities, using `s s⁻¹ = 1`.

## Scope

The module is algebra on the field `L` only. It does not construct trace-compatible cocycles
from root groups, and it does not construct `RootUnitaryCoordinates`.
