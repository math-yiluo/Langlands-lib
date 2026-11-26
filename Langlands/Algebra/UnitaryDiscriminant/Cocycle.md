# The determinant factor set of a twisted projective cocycle

Module `Langlands.Algebra.UnitaryDiscriminant.Cocycle`, namespace `Langlands.UnitaryDiscriminant`.

## Setting

`M/F` is a field extension, `G = M ≃ₐ[F] M`, `H` a subgroup of `G` and `I` a finite index type.
Write `ε(g) = 0` for `g ∈ H` and `ε(g) = 1` for `g ∉ H`. The twisted actions `twistGL H` on
`GL I M` and `twistUnit H` on `Mˣ` are those of `Langlands.Algebra.UnitaryDiscriminant.Lifts`:
`g(X)` and `g • a` for `g ∈ H`, `g(X)^{-T}` and `(g • a)⁻¹` for `g ∉ H`. The index-two hypothesis
is `hmul : ∀ g h, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H)`. A *twisted projective cocycle* is a family
`P : G → GL I M` with unit scalars `c : G → G → Mˣ` such that

```text
P g * twistGL H g (P h) = scalar (c g h) * P (g * h)        (all g, h).
```

## The definition

`detCocycle H P c m g h : Mˣ` is

```text
μ(g, h) = c(g, h)^m · g(det P_h)^{ε(g)} · (-1)^{m ε(g) ε(h)},
```

written in Lean as `c g h ^ m * (if g ∈ H then 1 else g • det (P h)) *
(if g ∉ H ∧ h ∉ H then (-1) ^ m else 1)`. The three cases are recorded by `detCocycle_of_mem`,
`detCocycle_of_not_mem_of_mem` and `detCocycle_of_not_mem_of_not_mem`.

## Results

* `detCocycle_isTwoCocycle`: under `hmul`, if `c` satisfies the `m`-th power of the twisted
  cocycle identity, `(c g h · c (gh) k)^m = (twistUnit g (c h k) · c g (hk))^m`, and the
  determinants satisfy `det P_g · twistUnit g (det P_h) = c(g, h)^{2m} · det P_{gh}`, then `μ` is an
  ordinary two-cocycle for the Galois action on `Mˣ`
  (`Langlands.ScalarTwoCocycle.IsTwoCocycle`: `μ(g,h) μ(gh,k) = g(μ(h,k)) μ(g,hk)`).
* `det_mul_twistUnit`: taking determinants of the twisted projective cocycle law gives the
  determinant hypothesis with exponent `card I`.
* `pow_twisted_of_lifts`: for `card I = 2m`, the power hypothesis holds; for `m ≥ 1` it is the
  `m`-th power of `UnitaryDiscriminant.twisted_cocycle`, and for `m = 0` both sides are `1`.
* `detCocycle_isTwoCocycle_of_lifts`: hence the determinant factor set of every twisted
  projective cocycle of size `2m` is a two-cocycle.
* `detCocycle_mul_self`: `μ(g, h)^2` is the coboundary of `g ↦ det P_g`,
  `det P_g · g(det P_h) · (det P_{gh})⁻¹`.
* `detCocycle_eq_coboundary_mul`: if `P' g = b(g) · P g` for unit scalars `b(g)`, and `c, c'` are
  factor sets of `P, P'`, then `detCocycle H P' c' m = coboundary (b^m) · detCocycle H P c m`.

## Proofs

**Cocycle identity.** Write `x = c(g,h)`, `y = c(gh,k)`, `z = c(h,k)`, `w = c(g,hk)` and
`d_t = det P_t`. Apply `g` to the determinant relation for `(h, k)`. The proof splits into eight
cases by the membership of `g, h, k` in `H`; `hmul` determines the membership of `gh` and `hk`.

* If `g ∈ H`, the factors `g(d_?)` do not occur in `μ(g, h)` and `μ(g, hk)`, the factors of
  `μ(gh, k)` and `g(μ(h, k))` agree (`(gh)(d_k) = g(h(d_k))` and `gh ∈ H ↔ h ∈ H`), and the
  identity is the power hypothesis `(xy)^m = (g(z) w)^m`.
* If `g ∉ H`, the power hypothesis reads `(xy)^m = (g(z)⁻¹ w)^m`, i.e. `(x y g(z))^m = w^m`.
  If `h ∈ H`, the determinant relation gives `g(d_h) (gh)(d_k) = g(z)^{2m} g(d_{hk})`; if
  `h ∉ H`, it gives `g(d_h) = g(z)^{2m} g(d_{hk}) (gh)(d_k)`. In each case the signs `(-1)^m` on the
  two sides agree, and the identity is a linear combination of these two relations.

In Lean each case is closed by passing to the field `M` (`Units.ext`) and `linear_combination`.

**Square.** If `g ∈ H`, `μ(g,h)^2 = c(g,h)^{2m} = d_g g(d_h) d_{gh}⁻¹` by the determinant relation.
If `g ∉ H`, the determinant relation is `d_g = c(g,h)^{2m} d_{gh} g(d_h)`, the sign squares to `1`
and `μ(g,h)^2 = c(g,h)^{2m} g(d_h)^2 = d_g g(d_h) d_{gh}⁻¹`.

**Rescaling.** Cancelling `P'(gh)` in the two cocycle laws and using injectivity of the scalar
embedding gives `c'(g,h) = b(g) · twistUnit g (b(h)) · c(g,h) · b(gh)⁻¹`, and
`det P'_h = b(h)^{2m} det P_h`. For `g ∈ H` the extra factor of `μ'` is `(b(g) g(b(h)) b(gh)⁻¹)^m`.
For `g ∉ H` it is `(b(g) g(b(h))⁻¹ b(gh)⁻¹)^m · g(b(h))^{2m}`, the same element. For empty `I`,
`m = 0` and every determinant is `1`, so both sides are `1`.

## Role and provenance

Provenance: derived. `μ` is the factor set of the descent of the middle exterior power. Let `Λ`
be the `m`-th exterior power on `GL_{2m}` and `J` the matrix of the exterior pairing
`Λ^m × Λ^m → Λ^{2m}` in the standard basis. Then `J Λ(X) J⁻¹ = det(X) Λ(X)^{-T}` and
`J^2 = (-1)^m`. The lifts `Q_g = Λ(P_g)` for `g ∈ H` and `Q_g = Λ(P_g) Jᵀ` for `g ∉ H` satisfy
`Q_g g(Q_h) = μ(g, h) Q_{gh}`. The paired page `Langlands/Algebra/UnitaryDiscriminant/Class.md`
gives this computation and its sources in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol,
*The Book of Involutions* (1998), §10. This module proves the cocycle and coboundary identities
directly from the twisted projective cocycle law; exterior powers do not occur in the Lean code.
With `H = ⊤`, the case without outer automorphisms, `μ = c^m`.
