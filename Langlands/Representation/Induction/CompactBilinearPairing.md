# Conditional bilinear integration on smooth induction

This internal construction integrates an actual complex bilinear coefficient
pairing on the existing smooth induced-function carriers. The group and the two
coefficient carriers have independent universes. The input representations are
representations of an arbitrary subgroup `P` of a topological group `G`; neither
coefficient carrier needs a topology or a norm.

For representations `τ` on `V` and `υ` on `W`, take
`b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ`. A supplied subgroup `K`, a measurable space on `K`, and a
measure `μ` specify the integration domain. For every actual smooth covariant
function `h` for `υ` and `f` for `τ`, assume explicitly that
`k ↦ b (h(k)) (f(k))` is integrable. Then `integralBilinearPairing` is the actual
complex bilinear map

```text
(h,f) ↦ ∫ k : K, b (h(k)) (f(k)) ∂μ.
```

There is no complex conjugation. The evaluation formula is
`integralBilinearPairing_apply`. The local constancy theorem
`bilinearPairing_isLocallyConstant` concerns the scalar function on all of `G`
and follows by combining local constancy of the two evaluations with the
arbitrary coefficient pairing. Local constancy alone is not used to assert
integrability for the supplied measurable space or measure.

`integralBilinearDualMap` also assumes the following equality for every ambient
`g : G` and every `h,f`:

```text
∫ k : K, b (h(k*g)) (f(k*g)) ∂μ = ∫ k : K, b (h(k)) (f(k)) ∂μ.
```

This gives an actual representation intertwiner from `smoothInduced P υ` into
the full algebraic dual of `smoothInduced P τ`. Invariance is required under
every element of `G`; invariance only under `K` would not suffice.
`integralBilinearSmoothDualMap` uses `smoothLift` and
`smoothInduced_smooth` to restrict the target to
`smoothContragredient (smoothInduced P τ)`. Smoothness of the resulting
functionals is proved by this construction and is not an additional hypothesis.
`integralBilinearSmoothDualMap_apply` gives the same scalar integral after the
existing smooth-dual evaluation pairing.

For independent further coefficient carriers, `integralBilinearPairing_map`
proves compatibility with actual coefficient intertwiners `A : υ → υ'` and
`B : τ → τ'` satisfying `b' (A w) (B v) = b w v`, with the same `K` and `μ`.
Each integral pairing has its own explicit integrability hypothesis.
`integralBilinearSmoothDualMap_natural` proves the corresponding equality of
actual intertwiners: apply induced `A`, then the primed smooth-dual map, then
pull back along induced `B`. Each smooth-dual map has its own explicit diagonal
invariance hypothesis.

The construction is derived internal mathematics. Its inputs are the published
smooth induction, smooth contragredient, smooth lifting, and Mathlib's scalar
Bochner integration. It makes no attribution to an unread external source.
Worker 166 implemented the construction; Worker 14 supplied design feedback
about the coefficient-map compatibility.

The proof of bilinearity applies `integral_add` using the supplied integrability
of each summand and `integral_smul` for scalar multiplication. For equivariance,
apply diagonal invariance to `h` and the right translate of `f` by `g⁻¹`. Right
translation by `g` then cancels the latter translation in the second argument.
This is exactly the inverse-argument action on the algebraic dual. Smooth lifting
preserves the underlying functional, so its evaluation formula is definitional.
Coefficient compatibility is equality of the scalar integrands; extensionality
of smooth functionals gives the intertwiner square.

The measure, integrability, and diagonal invariance are supplied inputs. This
module constructs no Haar measure and proves no GL parabolic specialization. It
requires no compactness, local compactness, admissibility, nondegeneracy,
finite-dimensionality, positive form, or equivalence. It asserts no perfectness
or bijectivity, and it does not establish natural induction duality, Jacquet
duality, second adjointness, or the comparison and head consequences.
