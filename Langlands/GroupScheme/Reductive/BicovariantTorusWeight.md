# Weights forced by bi-covariant coordinates at unit points

Worker 1628 derives this internal result from the Library's point form of left
covariance. It is a cancellation argument. Suppose a coordinate is covariant
on the left for one subgroup and on the right for another, and its value at a
point `m` is a unit. Whenever `m` intertwines a point of the first subgroup
with a point of the second, the two weights must agree there. The intended use
is for a Borel subgroup, its opposite and a torus normalized by `m`. There the
result forces the weight of the coordinate to be fixed by the Weyl element of
`m`. This file proves only the cancellation and assumes no torus, Weyl group or
Bruhat decomposition.

## Setting

Let `k` be a field and `G`, `H`, `Q`, `D` group schemes over `Spec k`; `G`,
`H` and `Q` have affine structure morphisms. Let `i : H → G` and `q : Q → G`
be actual homomorphisms, `χ` a coordinate of `H`, `ψ` a coordinate of `Q` and
`d` a coordinate of `G`, with two hypotheses:

- left covariance, `d ∈ leftCovariantSubspace i χ`, so that
  `d(i(h) g) = χ(h) d(g)` on every test scheme (the Library's
  `pointAlgebraHom_leftCovariant`);
- right inverse covariance, `d(g q(h')⁻¹) = ψ(h') d(g)` for all points
  `h' ∈ Q(T)` and `g ∈ G(T)` of every test scheme `T`. This is the form of
  condition 2 of `SteinbergBigCellStatement`, with `q = i ≫ inn(n)`.

Values of coordinates are taken with `pointAlgebraHom`.

## Declarations

- `pointAlgebraHom_eq_of_mul_eq_mul`: let `T` be a test scheme and
  `h ∈ H(T)`, `h' ∈ Q(T)`, `m ∈ G(T)` with `i(h) m = m q(h')`. If `d(m)` is a
  unit, then `χ(h) = ψ(h'⁻¹)`. Proof: left covariance gives
  `d(i(h) m) = χ(h) d(m)`. Right inverse covariance at the point `h'⁻¹` gives
  `d(m q(h'⁻¹)⁻¹) = ψ(h'⁻¹) d(m)`. Mathlib's `GrpObj.inv_comp` rewrites
  `q(h'⁻¹)⁻¹` as `q(h')`, so both left sides are `d(i(h) m)`. Cancelling the
  unit `d(m)` gives the claim.
- `isUnit_pointAlgebraHom_constantPoint`: if the value of `d` at a rational
  point `n` is a unit, so is its value at the constant point
  `constantPoint G n T` over every test scheme. The constant point is the
  pullback of `n` along `T → Spec k`, and evaluation commutes with pullback
  (`pointAlgebraHom_naturality`).
- `IsIntertwiningPoint i q jH jQ φ n`, for homomorphisms `jH : D → H`,
  `jQ : D → Q` and `φ : D → D` and a rational point `n` of `G`, is the
  proposition that `i(jH(t)) n = n q(jQ(φ(t)))` for all points `t` of `D` on
  every test scheme. Here `n` means `constantPoint G n T`. When `D` is a torus
  embedded in both subgroups and `n` normalizes it, `φ` is the induced
  automorphism of `D`.
- `pointAlgebraHom_comp_eq_of_normalizes`: if `IsIntertwiningPoint i q jH jQ φ n`
  holds and `d(n)` is a unit, then `χ(jH(t)) = ψ(jQ(φ(t))⁻¹)` for all points
  `t` of `D` on every test scheme. This is `pointAlgebraHom_eq_of_mul_eq_mul`
  with `h = jH(t)`, `h' = jQ(φ(t))` and `m` the constant point of `n`.

## Scope

The file proves no statement about tori, normalizers, Weyl groups,
stabilizers or Bruhat cells. Turning the weight identity into the conclusion
that `n` lies in the torus needs a separate trivial-stabilizer or
self-centralizer argument.
