# Completed Gauss-normed Laurent polynomials at a positive radius

Author: Worker 1010.

This helper module builds the field extension that the arbitrary-radius
spectral power proof uses for a radius `t > 0` none of whose nonzero integral
powers is the norm of an element of `K`. Throughout, `K` is a normed field
with an ultrametric norm. Completeness of `K` is used only for the retraction
at the end.

## Laurent polynomials with the Gauss norm

`GaussLaurent K t` is a type synonym for Mathlib's `AddMonoidAlgebra K ℤ`,
the Laurent polynomials over `K`. It carries the ring structure of that
algebra. `GaussLaurent.coeff p` is the finitely supported coefficient
function, `GaussLaurent.single k a` is the monomial `a T^k`, and
`GaussLaurent.C` is the ring map sending `a` to `a T^0`.

When `0 < t` (passed as `Fact (0 < t)`), the norm of `p` is the Gauss norm
\[
  \|p\| = \max_n \|p_n\|\, t^n ,
\]
the largest weighted coefficient norm over the finite support, where `n`
ranges over `ℤ`. It is defined in `NNReal` as a finite supremum
(`gaussNNNorm`). The module proves:

- this is an additive group norm (`gaussAddGroupNorm`);
- the norm is submultiplicative, giving a `NormedCommRing`;
- the norm is ultrametric.

Submultiplicativity uses the finite coefficient formula for a product. Each
term `p_i q_j` with `i + j = n` satisfies
`‖p_i‖ ‖q_j‖ t^n = (‖p_i‖ t^i)(‖q_j‖ t^j)`, and the ultrametric inequality
for finite sums finishes the bound. The characterizations `norm_le_iff`,
`norm_lt_iff` and `norm_coeff_mul_le` express the norm coefficientwise, and
`norm_single` computes the norm of a monomial as `‖a‖ t^k`.

`exists_dominant` uses the hypothesis
`H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n`. Under `H`, every nonzero `p`
has an index `k` with `‖p‖ = ‖p_k‖ t^k` and `‖p - p_k T^k‖ < ‖p‖`. Take `k`
where the maximum is attained. Suppose another index `n` reached the same
value. Then `‖p_n / p_k‖ = t^(k-n)` with `k - n ≠ 0`, which contradicts `H`.

## The completion and its field structure

`CompletedGaussLaurent K t` is Mathlib's metric completion of
`GaussLaurent K t`. It inherits a complete `NormedCommRing` structure. The
instance `completion_isUltrametricDist`, proved by density for every
ultrametric seminormed group, makes it ultrametric. The scalar map `ι` sends
`a` to the class of `a T^0` and is isometric (`norm_ι`). The class `X` of
`T^1` has norm `t` (`norm_X`).

Assume `H`. `exists_mul_eq_one_norm_le` shows that every nonzero `x` has an
inverse `v` with `‖v‖ ≤ ‖x‖⁻¹`. The proof has four steps.

1. By density there is a Laurent polynomial `p` with `‖x - p‖ < ‖x‖`. The
   ultrametric inequality then gives `‖p‖ = ‖x‖`.
2. Let `u = p_k T^k` be the dominant monomial of `p`. It is a unit of the
   Laurent ring with inverse `p_k⁻¹ T^(-k)`, and `‖u⁻¹‖ = ‖x‖⁻¹`. Since
   `‖x - u‖ < ‖x‖`, Mathlib's `Units.ofNearby` makes `x` a unit of the
   complete ring.
3. Its inverse `v` satisfies `v = u⁻¹ - u⁻¹ (x - u) v`.
4. Here `‖u⁻¹‖ ‖x - u‖ < 1`. So by the ultrametric inequality `‖v‖` cannot
   exceed `‖u⁻¹‖ = ‖x‖⁻¹`.

Consequently every element is a unit or zero (`isUnit_or_eq_zero`). The norm
is exactly multiplicative (`norm_mul_eq`): from `‖y‖ ≤ ‖v‖ ‖x y‖` one gets
`‖x‖ ‖y‖ ≤ ‖x y‖`. `field H` is Mathlib's `Field.ofIsUnitOrEqZero` structure
on the completed ring. `normedField H` combines it with the completed norm.

## The constant-term retraction

For complete `K`, `retraction` extends the constant-coefficient map
`p ↦ p_0` continuously to the completion. Its properties are proved by
density:

- `norm_retraction_le`: `‖retraction x‖ ≤ ‖x‖`, since `‖p_0‖ t^0 ≤ ‖p‖`;
- `retraction_ι_mul`: `retraction (ι a * x) = a * retraction x`;
- `retraction_one`: `retraction 1 = 1`.

## Provenance

This is an internal construction used to prove the arbitrary-radius
statement. It is not a formalization of a numbered result of the cited
lecture notes. It realizes the classical idea of extending the ground field
so that a non-strict radius becomes an actual absolute value. Berkovich,
*Non-Archimedean analytic spaces* (Trieste lectures, 2009), Fact 2.1.3(ii) on
page 7 records that the radius-`r` Tate algebra is strictly affinoid exactly
when `r` lies in `√|k*|`. The Laurent field here supplies such absolute values
for the radii outside this group. All proofs above are the implemented Lean
proofs. No property of the field, its norm or its retraction is assumed.
